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
// Description      :This module manipulates the status pointer and controls 
//                   parsing of the linked list to move the frame from the 
//                   SRAM to the FIFO. Frame lifetime and length of 
//                   frame is checked in this module.  
// Simulation Notes : System verilog assertions can be enabled with RW_ASSERT_ON
//                    Then a system verilog capable simulator is needed
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
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module txListProc(
        //$port_g clock and reset
        input  wire         macPITxClk,                     //MAC Platform 1 Clk. 80 MHz. 
        input  wire         macPITxClkHardRst_n,            //Hard Reset synchronized to macPITxClk.
        input  wire         macPITxClkSoftRst_n,            //Soft Reset synchronized to macPITxClk.
        
        
        //$port_g primary controller interface
        input  wire [31:0]  statusPointer,                  //Status pointer from Primary Controller.
        input  wire         trigTxListProc,                 //Trigger from the Primary Controller. Indicates
                                                            //packet linked list has to be parsed and packet started
                                                            //to fetch
        input  wire         abortTx_p,                      //stop from the MAC Controller. Indicates abort transmission.
        //
        output wire         trigHalt_p,                     //Trigger Primary Controller FSM to HALTED
        output wire         trigDead_p,                     //Trigger Primary Controller FSM to DEAD
        output wire         lifetimeExpired_p,              //Lifetime expired for the current MPDU
        output reg          txFIFOFlushDone_p,              //Signal indicating the completion of the txFifo Flush
        output wire         txFIFOFlushDMA,                 //Signal to Flush the FIFO
                                                            //Discard the previously transferred Header descriptor
        output wire         discardPrevHD_p,                //parameters. Signal to TX Parameter Cache module
                                                            //whichDescriptor field in the Header descriptor
        output wire         nxtMpduDescValid,               //Indicates the next MPDU Descriptor is valid
        output wire         atomicFrmValid_p,               //Indicates next atomic frm ptr is valid
        output wire         plyTblValid,                    //Indicates validity of policy table address
        output reg   [31:0] nxtAtomFrmPtr,                  //Next Atomic Frame Exchange Pointer connected to Transmit Staus
                                                            //Updater
        output reg          patternError,                   //To the Status Updater block. Indicates there has
                                                            //been a pattern error
        output wire         ptError,                        // Transmit PolicyTable Error

        //$port_g Tx Fifo interface
        input  wire         txFifoEmpty,                    //TX FIFO empty signal
        input  wire         txFifoAlmostFull,               //TX FIFO Almost FULL status indication.
        input  wire         txFifoFull,                     //When HIGH indicates there is only one quadlet space left
        //
        output reg          txFifoWr,                       //Write signal to TX FIFO
        output wire  [31:0] txFifoWrData,                   //Write data to TX FIFO
        output reg   [ 5:0] txTagFifoWrData,                //Write signal to TX TAG FIFO
        
        //$port_g Status updater interface
        input  wire         noFrm2Update,                   //From StatusUpdater. Indicates there are no frames for
                                                            //whome the status is expected
        input  wire         txCtrlRegBusy,                  //From Parameter Cache module. Is asserted high when
                                                            //both the registers are populated.
        input  wire         updateDMAStatus_p,              // trigs the DMA Status update.
        input  wire         retryFrame_p,                   //Retry indication from MAC Controller
        input  wire         trigNxtAtomFrm_p,               //From Transmit Status Updater. Is asserted when the retry limit
                                                            //is reached for a MSDU fragment and the next atomic frame should
                                                            //be fetched
        input  wire         mpduCtrFull,                    //From Transmit Status Updater. Is asserted when the txStatus
                                                            //Updater holds parameters for 2 MPDU's
        input  wire         prevFrmRts,                     //Indicates previous transmitted frame is RTS
        input  wire  [31:0] tsfTimerValue,                  //TSF Timer
        //
        output reg          storeParameters_p,              //Signal to Status Updater to store the parameters
                                                            //for the current MPDU
        output reg          storeAMPDUParameters_p,         //Signal to Status Updater to store the parameters
                                                            //for the current A-MPDU
        output wire         updStatusPtr_p,                 //Indication to the Status Update to trigger the
                                                            //active channel for a status pointer update
        output wire [31:0]  statusPtr2Upd,                  //StatusPtr should be updated to this pointer value
                                                            //if the updStatusPtr_p is asserted
        output reg  [31:0]  currentPtr,                     //currentPtr value /* synthesis syn_keep = 1 */
        
        output reg  [31:0]  statusInformationReg,           // value of status information register
        
        //$port_g Tx parameters cache
        output wire         txCtrlRegWr,                    //Write signal to the txControl registers
        output wire         txCtrlRegHD,                    //Indicates whenever the txCtrlRegWr is high
                                                            //the Header descriptor parameters are being
                                                            //passed
        output wire         txCtrlRegPT,                    //Indicates whenever the txCtrlRegWr is high
                                                            //the Policy Table parameters are being
                                                            //passed
        
        //$port_g interrupt controller port
        output reg          interruptEnTx,                  //InterruptEnTx bit in MAC_CONTROL2 quadlets in THD
        output wire         bufferInterruptTx,              //bufferInterruptTx bit in Status quadlets in TPD
        
        
        //$port_g dma Arbiter interface
        input  wire         txListProcGrant,                //Grant for the recieve list processor 
        //
        output reg          txListProcReq,                  //Transmit List Processor request for grant from arbiter
        
        //$port_g RdWrite controller interface
        output reg          txListRead,                     // Request to the read write controller to perform a
                                                            // read operation from the SRAM. The number of quadlets
                                                            // to be read is given by the numQuadlets signal
        output reg          txListWrite,                    // Request to the read write controller to perform a
        output wire  [ 2:0] txListSize,                     // Access size
        output reg   [31:0] txListStartAddress,             // Starting address of the burst to be performed
        output reg          txListLast,                     // Last read access
        output wire  [31:0] txListWriteData,                // The data writes by the Read Write controller to Local SRAM
        //
        input  wire  [31:0] txListReadData,                 // The data read by the Read Write controller from Local SRAM
        input  wire         txListReadDataValid,            // Data in txListReadData is valid when this signal is
        input  wire         txListNextData,                 // 
                                                            // asserted HIGH 
        input  wire         txListTransComplete,            // transaction done
        input  wire         txListError,                    // If an error happened during dmaHIF transaction
                                                            
        output wire         txListProcIdle,                 // indicate the list processor is idle
 
        input  wire         staUpdTransComplete,            // indicate the status update is done
 
        //$port_g Debug interface
        output reg   [ 4:0] txListProcCs,                   // Current State counter                                                
        output wire [15:0]  debugPortDMA3,                  // txListProc Debug Port
        output wire [15:0]  debugPortDMA6,                  // txListProc Debug Port
        output wire [15:0]  debugPortTxListA                // txList AHB read access debug
         );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// txListProc FSM states definition
//$fsm_sd txListProc
localparam
  IDLE                     = 5'd0,     //When not active FSM is in this state.
  CHK_MPDU_CNT             = 5'd1,     //Checks the number of MPDU in txfifo.
  UPD_CURR_PTR             = 5'd2,     //Updates the current pointer to the 
                                       //status pointer or next mpdu pointer
                                       //or next atomic frame exchange pointer
  FETCH_HDR_DESC           = 5'd3,     //req the rd wr ctlr to fetch hdr desc
  WAIT_FETCH_HDR_DESC_DONE = 5'd4,     //wait for hdr desc to be fetched
  PROC_HDR_DESC            = 5'd5,     //check if hdr desc fields are correct
  DISCARD_PREV_HD          = 5'd6,     //discard the recently fetched THD 
  TRIG_STATPTR_UPD         = 5'd7, 
  FETCH_PLY_TBL            = 5'd8,     //req to fetch policy table 
  WAIT_FETCH_PLY_TBL_DONE  = 5'd9,     //wait till policy table fetch is done
  PROC_PLY_TBL             = 5'd10,    //waits for policy table to be fetched
  WR_DATA_TX_FIFO          = 5'd11,    //req towrite the data from RAM to FIFO.
  WR_DATA_TX_FIFO_DONE     = 5'd12,    //waits for write of data to FIFO done.
  CHK_BUFFER_DESC_VALID    = 5'd13,    //checks if buffer/mpdu desc is valid.
  FETCH_PLD_DESC           = 5'd14,    //req to fetch the buffer descriptor
  WAIT_FETCH_PLD_DESC_DONE = 5'd15,    //waits for buffer descriptor is fetched
  WAIT_FOR_STATUS_UPDATE   = 5'd16,    //The MPDU counter is incremented 
  TX_FIFO_FLUSH            = 5'd17,    //Flush the TX FIFO signal is generated
  ERROR                    = 5'd18,    //when an error occurs this state is 
                                       //entered.
  RETURN_TO_IDLE           = 5'd19,    //if the Primary cotnroller has to be triggered to HALTED then this
                                       //state is entered/
  UPDATE_PLD               = 5'd20,    //req to update the Transmit Payload Descriptor Status
  WAIT_UPDATE_PLD_DONE     = 5'd21;    //waits for the completion of the Transmit Payload descriptor status
    

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// String definition to display txListProc current state
reg [24*8:0] txListProcCs_str;
`endif // RW_SIMU_ON


// manage transaction
reg         transactionEnable_p;  // this signal indicate the start of a transaction on the AHB
reg  [15:0] transactionSize;      // this signal indicate the transaction size
wire        transactionDone_p;    // this signal indicate the end of the transaction
reg         ongoingTransaction;   // when a transaction requested, this signal is assserted until all the data are transfered
reg         abortTransaction;     // when a transaction abort is requested
reg         ongoingBurst;         // indicate the a burst is ongoing
wire        burstStart_p;         // indicate a burst should be started
reg         burstStop_p;          // indicate a burst should be stop
reg  [15:0] remainingData;        // this signal indicate the number of byte to transfer remaining
wire        suspendRead;          // indicate the read to the memory should be suspended


//Internal Register Declarations
// reg         updToStatPtr;         // When asserted High indicates the current ptr
//                                   // should be updated to Status pointer  
reg         trigNxtAtomFrmReg_p;  // Delayed version of trigNxtAtomFrm_p used in 
                                  // moving from TX_FIFO_FLUSH state for retryLimit                       
                                  // Reached cases                                                        

reg         descriptorDoneTx;     // value of descriptorDoneTx from the header desc                       
reg         retryFrame;           // Latches the retry indication given by MAC Ctlr                       

reg         updNxtAtomFrm;        // update to next Atomic Frame exchange pointer                         
reg         updNxtMpdu;           // update to next MPDU pointer.                                         

reg         startMpdu;            // Start of MPDU indication to the TAG FIFO                             
reg         ampduHdr;             // when asserted indicates the curr desc is A-MPDU                      
                                  //  header descriptor                                                   
reg         ptFragment;           // when asserted indicates the curr desc need to fetch the policy table 
reg         writeMH;              // when asserted indicates the macHeader is written to Tx FIFO          
 
reg  [ 4:0] txListProcNs;         // Next State counter.                                                  
reg  [15:0] quadletsRead;         // count of number of quadlets read for current trsfr                   
reg  [31:0] polEntryAddr;         // Policy Entry address pointer from hdr descr                          
reg  [31:0] frameLifetime;        // Gives the lifetime from the header descr                             

reg  [31:0] nxtMpduDescPtr;       // the next MPDU descriptor pointer is stored                           
reg  [31:0] pldBufDescPtr;        // Current Payload Buffer descriptor pointer                            
reg  [31:0] nxtPldBufDescPtr;     // Next Payload Buffer descriptor pointer                               

reg  [31:0] dataStartPtr;         // Data Start pointer for the associated descr                          
reg  [31:0] dataEndPtr;           // Data End pointer for the associated descr                            

reg  [15:0] numQuadlets;          // Indicates the number of quadlets to be transferred for the           
                                  // current dmaHIF request                                               
//Internal Wire Declarations
        
wire        nxtAtomFrmPtrValid;   // validity of next Atomic Frame exchange Pointer
wire [1:0]  tagSelect;
// wire [1:0]  byteInfo;
wire        firstQuadlet;
wire        lastQuadlet;

wire        pldBufDescValid;      // indicates validity of first buffer descriptor

wire        bufferValid_p;        // Indicates next buffer pointer is valid
wire        mpduValid_p;          // indicates next MPDU descr ptr is valid 

wire        endMpdu;              // End of MPDU indication to the TAG FIFO

wire [15:0] bufLengthInQuads;     // Buf length in Quadlets

reg         waitFirstDataWord;    // Indicate the first Tx data is not yest written in Fifo
reg         waitingTransEnd;      // Indicates we are waiting the end of the transaction

wire        pointerNotAligned;    // Indicate one of the descriptor pointer is not aligned
reg         lifeTimeExpiredFlag;  // Indicate a life time expired has been detected

reg   [1:0] whichDesc;            // Given to status updater block

reg         patternError_gen;

wire        nextFrameLifetimeExpired_p;
reg         nextFrameLifetimeExpiredFlag;
reg         lifetimeExpiredEn;

wire        dataStartPtrNull;

reg [31:0]  curStatusTPDValue;
reg [31:0]  updStatusTPDPtr;               // pointer to the current Transmit Buffer Descriptor
reg [31:0]  updStatusTPDValue;             // Value of the current Transmit Buffer Descriptor Status
wire        updStatusTPD_p;                // value of status information register
        
reg         usePldDesc;
reg         bufferInterruptEnTx;           //bufferInterruptTx bit in Status quadlets in TPD

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


//Logic for currentState.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txListProcCs <= IDLE;
  else if (macPITxClkSoftRst_n == 1'b0)
    txListProcCs <= IDLE;
  //On abort from the DMA Primary Controller or retry 
  //indication from MAC Controller, FSM moves to FIFO flush state.
  else if (abortTx_p        == 1'b1 ||
           retryFrame_p     == 1'b1 ||
           trigNxtAtomFrm_p == 1'b1 )
    txListProcCs <= TX_FIFO_FLUSH;
  else 
    txListProcCs <= txListProcNs;
end
 
//Logic for Next State
always @*
begin
  case (txListProcCs)
    IDLE:
      //$fsm_s At reset the FSM begins in this state.
      if (trigTxListProc || retryFrame)
        //$fsm_t When a trigger from the Primary Controller trigTxListProc 
        //is received the Transmit List Processor starts its process
        //of moving descriptor and associated buffer from SRAM to TX FIFO.
        //Also the FSM moves of out of IDLE when a frame is beign retried. 
        //When the retry frame indication is given by MAC Controller retryFrame
        //the FSM immediately moves to CHK_MPDU_CNT state. 
        //To start fetching the same descriptor and buffers the 
        //registered version of retryFrame_p, retryFrame triggers this movement
        txListProcNs = CHK_MPDU_CNT;
      else 
        //$fsm_t While no trigger is received from the MAC Controller, the FSM stays in IDLE
        txListProcNs = IDLE;

    CHK_MPDU_CNT:
      //$fsm_s The TX Parameter cache module will give a txCtrlRegBusy signal
      if (txCtrlRegBusy       == 1'b1 ||
          mpduCtrFull         == 1'b1 ||
          lifeTimeExpiredFlag == 1'b1
         )
        //$fsm_t If the TX Parameter cache has reached the number of MPDU parameters it can store.
        //Then this FSM waits in CHK_MPDU_CNT until the TX Controller has finished processing
        //before fetching the next MPDU for transmission
        // In this state the txCtrlRegBusy signal is checked. If it is high indicates there are 2 MPDU?s in the TX FIFO. 
        txListProcNs = CHK_MPDU_CNT;
      else
        //$fsm_t if the TX Parameter cache can accept a new MPDU parameters, the FSM moves to UPD_CURR_PTR
        txListProcNs = UPD_CURR_PTR; 

    //currentPtr is updated in this state
    UPD_CURR_PTR:
      //$fsm_s In this state :
      // - The currentPtr is updated to the statusPtr if updToStatPtr is asserted. 
      // - The currentPtr is updated to the Next MPDU Descriptor Pointer if updNxtMpdu is asserted
      // - The currentPtr is updated to the Next Atomic Frame Exchange Sequence Counter if updNxtAtomFrm is asserted. 
      // - The signals updToNxtMpduPtr and updToNxtFrmPtr are deasserted
      
      //$fsm_t The FSM moves to FETCH_HDR_DESC after 1 clock cycle
      txListProcNs = FETCH_HDR_DESC;
 
    FETCH_HDR_DESC:
      //$fsm_s In this state, ahbRead is asserted. 
      //The startAddress is assigned to the currentPtr. The numQuadlets is assigned to the size of the header descriptor.
      
      //$fsm_t The FSM moves to WAIT_FETCH_HDR_DESC_DONE after 1 clock cycle
      txListProcNs = WAIT_FETCH_HDR_DESC_DONE;

    WAIT_FETCH_HDR_DESC_DONE:
      //$fsm_s The FSM waits in this state until the complete header descriptor is
      //fetched. 
      if (patternError_gen   == 1'b1 ||  // the unique patter is not found or
          txListError        == 1'b1 ||  // the hostIf returns an error or
          pointerNotAligned  == 1'b1     // the pointer is not aligned 
         )
        //$fsm_t If there is an dmaHIF error or a descriptor error then the 
        //FSM moves to ERROR state and triggers the active primary cotnroller
        //to DEAD
        // The error type can be :
        //   - the unique patter is not found or
        //   - the hostIf returns an error or
        //   - the pointer is not aligned 
        txListProcNs = ERROR;
      else if (transactionDone_p == 1'b1)
        //$fsm_t When transactionDone_p is received indicating that the fetch of the Header descriptor is completed, 
        //the FSM moves to PROC_HDR_DESC 
        txListProcNs = PROC_HDR_DESC;
      else 
        //$fsm_t When transactionDone_p is not received indicating that the fetch of the Header descriptor is still ongoing, 
        //the FSM stays in WAIT_FETCH_HDR_DESC_DONE 
        txListProcNs = WAIT_FETCH_HDR_DESC_DONE;
    
    PROC_HDR_DESC:
      //$fsm_s waits for the complete fetch of the header
      //to be over and processes the different 
      //fields
      if (descriptorDoneTx           == 1'b1 || 
          lifetimeExpired_p          == 1'b1 || 
          nextFrameLifetimeExpired_p == 1'b1   )
        //$fsm_t if the descriptorDoneTx bit or lifetime is 
        //expired then discard the previous fetched
        //header descriptor parameters and the FSM moves to DISCARD_PREV_HD.
        txListProcNs = DISCARD_PREV_HD;
      else if (ampduHdr == 1'b1 || ptFragment == 1'b1)
      begin
        if (plyTblValid == 1'b0)
          //$fsm_t For an AMPDU only if it is a header
          //descriptor the policy table should be 
          //fetched but the Policy table is invalid, the FSM moves to ERROR
          txListProcNs = ERROR;
        else
          //$fsm_t For an AMPDU only if it is a header
          //descriptor the policy table should be 
          //fetched, the FSM moves to FETCH_PLY_TBL
          txListProcNs = FETCH_PLY_TBL;
      end
      else if (dataStartPtrNull)
        //$fsm_t If the data buffer start pointer associated with the current header descriptor is null, 
        // the FSM moves to CHK_BUFFER_DESC_VALID to fetch the Payload Buffer
        txListProcNs = CHK_BUFFER_DESC_VALID;
      else 
        //$fsm_t If all the check indicates that the data buffer associated with the current header descriptor should 
        //be fetched, the FSM moves to WR_DATA_TX_FIFO.
        txListProcNs = WR_DATA_TX_FIFO;

    DISCARD_PREV_HD:
      //$fsm_s In this state the discardPrevHD_p signal is asserted to indicate to the TX Parameter Cache Module 
      //to discard the Previous stored parameters.
      if (descriptorDoneTx == 1'b1) 
      begin
        if ((whichDesc == 2'b00 &&
             nxtAtomFrmPtrValid == 1'b0) ||
            (whichDesc != 2'b00 &&
             nxtMpduDescValid == 1'b0)
           )
        begin
          if (noFrm2Update)
            //$fsm_t If the current descriptor is done but the next is not valid and no status update is pending,
            //the FSM moves to  RETURN_TO_IDLE
            txListProcNs = RETURN_TO_IDLE;
          else
            //$fsm_t If the current descriptor is done but the next is not valid and a status update is pending,
            //the FSM moves to WAIT_FOR_STATUS_UPDATE. 
            txListProcNs = WAIT_FOR_STATUS_UPDATE;
        end
        else
            //$fsm_t If the current descriptor is done and the next is valid ,
            //the FSM moves to TRIG_STATPTR_UPD. 
          txListProcNs = TRIG_STATPTR_UPD;
      end
      else 
      begin
        if (nxtAtomFrmPtrValid == 1'b0)
        begin
          if (noFrm2Update)
            //$fsm_t If the current descriptor is not done but the next is not valid and no status update is pending,
            //the FSM moves to  RETURN_TO_IDLE
            txListProcNs = RETURN_TO_IDLE;
          else
            //$fsm_t If the current descriptor is not done but the next is not valid and a status update is pending,
            //the FSM moves to  WAIT_FOR_STATUS_UPDATE
            txListProcNs = WAIT_FOR_STATUS_UPDATE;
        end
        else if (lifeTimeExpiredFlag == 1'b1 )
          //$fsm_t Incase of lifetime expiry the FSM has to move to the next
          //Atomic frame sequence pointer. Hence, the FSM moves to TRIG_STATPTR_UPD
          txListProcNs = TRIG_STATPTR_UPD;
        else if (nextFrameLifetimeExpiredFlag == 1'b1)
          //$fsm_t Incase of lifetime expiry the FSM has to move to the next
          //Atomic frame sequence pointer. Hence, the FSM moves to WAIT_FOR_STATUS_UPDATE
          txListProcNs = WAIT_FOR_STATUS_UPDATE;
        else
            //$fsm_t If the current descriptor is not done but the next is valid,
            //the FSM moves to CHK_MPDU_CNT
          txListProcNs = CHK_MPDU_CNT;
      end
 
    TRIG_STATPTR_UPD:
      //$fsm_s This state is reached when the descriptorDoneTx bit is
      //set and next Atomic Frame Pointer is valid or next MPDU
      //descriptor pointer is valid. Here if the currentPtr and the 
      //status ptr are the same the status ptr of the current active  
      //channel is triggered for updation. This is because if the newTail
      //bit is set and if the first frame encountered is a descriptorDoneTx
      //then the status ptr is pointing to this location whereas the next 
      //frame is fetched and transmitted. When the status for the transmtted
      //frame is received the location of the status ptr is updated. So it is 
      //imperative incases of currentPtr adn the statusPtr being the same and 
      //descriptorDoneTx is set the statusPtr is immediately moved to the enxt
      //valid descriptorPtr.

      //$fsm_t The FSM moves to CHK_MPDU_CNT after 1 clock cycle
      txListProcNs = CHK_MPDU_CNT;

    FETCH_PLY_TBL:
      //$fsm_s Fetch policy table request is asserted
      //ahbRead is asserted. 
      //startAddress is assigned to the polEntryAddr. 
      //numQuadlets is assigned to the size of the Policy Table

      //$fsm_t The FSM moves to WAIT_FETCH_PLY_TBL_DONE after 1 clock cycle
      txListProcNs = WAIT_FETCH_PLY_TBL_DONE;
 
    WAIT_FETCH_PLY_TBL_DONE:
      //$fsm_s Wait for policy table fetch to be completed.
      if (patternError_gen == 1'b1 ||
          txListError      == 1'b1
         )
        //$fsm_t If either pattern error or dmaHIF transaction error
        //is received then move to ERROR where the active 
        //primary controller is triggered to DEAD 
        txListProcNs = ERROR;
      else if (transactionDone_p == 1'b1)
        //$fsm_t When the fetch of policy table is completed, the FSM moves to PROC_PLY_TBL
        txListProcNs = PROC_PLY_TBL;
      else
        //$fsm_t While the fetch of policy table is not completed, the FSM tays in WAIT_FETCH_PLY_TBL_DONE
        txListProcNs = WAIT_FETCH_PLY_TBL_DONE;
  
    PROC_PLY_TBL:
      //$fsm_s Incase this was a AMPDU Header descriptor then the next operation should be to fetch the next MPDU descriptor 
      //else fetch the header buffer 
      if (ampduHdr == 1'b1)
      begin
        if (nxtMpduDescValid == 1'b1)
          //$fsm_t If frame is an AMPDU header and the next MPDU descriptor is valid then the FSM goes to CHK_MPDU_CNT.
          txListProcNs = CHK_MPDU_CNT;
        else if (noFrm2Update)
          //$fsm_t If frame is an AMPDU header and the next MPDU descriptor is not and no status is pending, then the FSM goes to RETURN_TO_IDLE.
          txListProcNs = RETURN_TO_IDLE;
        else  
          //$fsm_t If frame is an AMPDU header and the next MPDU descriptor is not and no status is pending, then the FSM goes to WAIT_FOR_STATUS_UPDATE.
          txListProcNs = WAIT_FOR_STATUS_UPDATE;
      end
      else if (dataStartPtrNull)
        //$fsm_t If the data buffer start pointer associated with the current header descriptor is null, 
        // the FSM moves to CHK_BUFFER_DESC_VALID to fetch the Payload Buffer
        txListProcNs = CHK_BUFFER_DESC_VALID;
      else
        //$fsm_t If frame is not an AMPDU header, the FSM moves to WR_DATA_TX_FIFO.
        txListProcNs = WR_DATA_TX_FIFO;

    WR_DATA_TX_FIFO:
      //$fsm_s Request to start moving data associated with buffer
      //is asserted in this state

      //$fsm_t The FSM moves to WR_DATA_TX_FIFO_DONE after 1 clock cycle
      txListProcNs = WR_DATA_TX_FIFO_DONE;

    WR_DATA_TX_FIFO_DONE:
      //$fsm_s Wait till the buffer is read completely.
      if (txListError == 1'b1)
        //$fsm_t If an error occurs during the data copy from the SRAM to the TX FIFO, the FSM moves to ERROR  
        txListProcNs = ERROR;
      else if (transactionDone_p == 1'b1)
      begin
        if (usePldDesc)
          //$fsm_t Once the data are fetched, the FSM moves to UPDATE_PLD state
          txListProcNs = UPDATE_PLD;
        else
          //$fsm_t Once the data are fetched, the FSM moves to CHK_BUFFER_DESC_VALID state
          txListProcNs = CHK_BUFFER_DESC_VALID;
      end
      else
        //$fsm_t While the fetch of the data is not completed, the FSM stays in WAIT_FETCH_PLD_DESC_DONE
        txListProcNs = WR_DATA_TX_FIFO_DONE;

    CHK_BUFFER_DESC_VALID:
      //$fsm_s In this state it is checked if the next payload descr
      //is valid if not then the next mpdu descr is valid or the 
      //next atomic frame exchange descr is valid. If nothing is valid
      //then SW has not programmed any more queue so move the primary
      //controller to HALTED. if payload descriptor is valid then
      //we are fetching for the same MPDU. If the payload descriptor is 
      //not valid then the current MPDU is fetched completely.
      if (bufferValid_p == 1'b1)
        //$fsm_t If the nextpayload  buffer descriptor is valid, the FSM moves to FETCH_PLD_DESC
        txListProcNs = FETCH_PLD_DESC;
      else if (mpduValid_p == 1'b1 ||
               atomicFrmValid_p == 1'b1)
        //$fsm_t If the next buffer descriptor is not valid
        //check for next MPDU or atomic frame exchange and 
        //if valid go to CHK_MPDU_CNT before fetching 
        txListProcNs = CHK_MPDU_CNT;
      else
        //$fsm_t If none of the descriptors are valid then the FSM moves to WAIT_FOR_STATUS_UPDATE state
        txListProcNs = WAIT_FOR_STATUS_UPDATE;

    FETCH_PLD_DESC:
      //$fsm_s Trigger the dmaHIF read write controller module to fetch 
      //payload descriptor
      // ahbRead is asserted. 
      // startAddress is assigned to the pldBufDescPtr. 
      // numQuadlets is assigned to the size of the Payload Descriptor

      //$fsm_t The FSM moves to WAIT_FETCH_PLD_DESC_DONE after 1 clock cycle
      txListProcNs = WAIT_FETCH_PLD_DESC_DONE;
 
    WAIT_FETCH_PLD_DESC_DONE:
      //$fsm_s Wait until the payload descriptor is completed fetched 
      if (patternError_gen  == 1'b1 ||
          txListError       == 1'b1 ||
          pointerNotAligned == 1'b1 )
        //$fsm_t If an error occurs during the payload descriptor fetch, the FSM moves to ERROR  
        txListProcNs = ERROR;
      else if (transactionDone_p == 1'b1)
        //$fsm_t Once the payload descriptor is fetched the DMA should fetche
        //the data from the buffer associated with this descriptor. hence
        //moves to WR_DATA_TX_FIFO state
        txListProcNs = WR_DATA_TX_FIFO;
      else
        //$fsm_t While the fetch of the payload descriptor is not completed, the FSM stays in WAIT_FETCH_PLD_DESC_DONE
        txListProcNs = WAIT_FETCH_PLD_DESC_DONE;

    WAIT_FOR_STATUS_UPDATE:
    //$fsm_s Waits for the status to be updated for the frame pointed by the currentPtr. 
      if (noFrm2Update == 1'b1)
        //$fsm_t If all the frame update have been done, the FSM moves to RETURN_TO_IDLE
        txListProcNs = RETURN_TO_IDLE;
      else 
        //$fsm_t While there is pending status update indicated by noFrm2Update flag, the FSM stays in WAIT_FOR_STATUS_UPDATE
        txListProcNs = WAIT_FOR_STATUS_UPDATE;
       
    TX_FIFO_FLUSH:
      //$fsm_s Waits until the FIFO goes empty and the read write controller FSM is IDLE.
      //The signal to flush the FIFO is generated here. 
      //waiting for fifoempty and Read Write Controller FSM IDLE ensures next transfer when started is clean 
      if (trigNxtAtomFrmReg_p == 1'b1)
        //$fsm_t If the trigNxtAtomFrmReg_p pulse is received, the FSM moves to UPD_CURR_PTR
        txListProcNs = UPD_CURR_PTR;
      else if (txFifoEmpty == 1'b1)
        //$fsm_t When the tx FIFO Empty flag is set indicating the completion of the TXFIFO flush,
        //the FSM moves back to IDLE
        txListProcNs = IDLE;
      else
        //$fsm_t While the TX FIFO is not empty, the FSM stays in TX_FIFO_FLUSH
        txListProcNs = TX_FIFO_FLUSH;

    UPDATE_PLD:
      //$fsm_s 

      //$fsm_t If the trigNxtAtomFrmReg_p pulse is received, the FSM moves to WAIT_UPDATE_PLD_DONE
      txListProcNs = WAIT_UPDATE_PLD_DONE;

    WAIT_UPDATE_PLD_DONE:
      //$fsm_s Wait until the payload descriptor is completed fetched 
      if (transactionDone_p == 1'b1)
        //$fsm_t Once the payload descriptor is updated
        txListProcNs = CHK_BUFFER_DESC_VALID;
      else
        //$fsm_t While the update of the payload descriptor is not completed, the FSM stays in WAIT_UPDATE_PLD_DONE
        txListProcNs = WAIT_UPDATE_PLD_DONE;


    ERROR:
      //$fsm_s The FSM moves to this state either on policy table 
      //being invalid or dmaHIF bus error or DMA pattern error 
      //the trigger for DMA error is generated

      //$fsm_t The FSM moves to TX_FIFO_FLUSH after 1 clock cycle
      txListProcNs = TX_FIFO_FLUSH;

    RETURN_TO_IDLE:
      //$fsm_s In this state hte active primary controller trigger to 
      //move to HALTED is generated

      //$fsm_t The FSM moves to IDLE after 1 clock cycle
      txListProcNs = IDLE;
 
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default: 
      txListProcNs = IDLE;
    // pragma coverage block = on 

  endcase
end 

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txFIFOFlushDone_p  <= 1'b0;
  else
  begin
    if ((txListProcCs == TX_FIFO_FLUSH) && txFifoEmpty)
      txFIFOFlushDone_p  <= 1'b1;
    else
      txFIFOFlushDone_p  <= 1'b0;
  end
end


// handle the management of the arbiter requests
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    waitingTransEnd  <= 1'b0;
    txListProcReq    <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    waitingTransEnd  <= 1'b0;
    txListProcReq    <= 1'b0;
  end
  else
  begin
    if (abortTransaction == 1'b1)
    begin  
      txListProcReq    <= 1'b0;
      waitingTransEnd  <= 1'b0;
    end
    else
    begin
      if (burstStart_p == 1'b1)
        txListProcReq <= 1'b1;
      else if (burstStop_p == 1'b1 || (txListProcCs == WAIT_UPDATE_PLD_DONE && txListNextData))
        txListProcReq    <= 1'b0;
      else if (txListProcCs == UPDATE_PLD)
        txListProcReq    <= 1'b1;

      if ((txListTransComplete == 1'b1) || (burstStart_p == 1'b1))
        waitingTransEnd  <= 1'b0;
      else if ((burstStop_p == 1'b1) && (txListTransComplete == 1'b0))
        waitingTransEnd  <= 1'b1;
    end
  end
end

// generate the end of transaction signal
assign transactionDone_p = (txListTransComplete == 1'b1 && remainingData == 16'b0) ? 1'b1 : 1'b0;

// manages the transaction
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    transactionEnable_p <= 1'b0;
    ongoingTransaction  <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    transactionEnable_p <= 1'b0;
    ongoingTransaction  <= 1'b0;
  end
  else
  begin
    if (abortTransaction == 1'b1)
      ongoingTransaction  <= 1'b0;
    else
    begin
      // latch the transaction status
      if (transactionEnable_p == 1'b1)
        ongoingTransaction  <= 1'b1;
      else if (transactionDone_p == 1'b1)
        ongoingTransaction  <= 1'b0;
    end
    // generate the start transaction signal
    if (ongoingTransaction == 1'b0)
    begin
      if ((txListProcCs == FETCH_HDR_DESC)  ||
          (txListProcCs == FETCH_PLY_TBL)   ||
          (txListProcCs == WR_DATA_TX_FIFO) ||
          (txListProcCs == UPDATE_PLD)      ||
          (txListProcCs == FETCH_PLD_DESC) )
      transactionEnable_p <= 1'b1;
    end
    else
    begin
      transactionEnable_p <= 1'b0;
    end
  end
end


// handle the management of the transaction abort
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    abortTransaction  <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    abortTransaction  <= 1'b0;
  end
  else
  begin
    if (ongoingTransaction == 1'b1)
    begin
      if ( (txListProcCs     == ERROR)         ||
           (txListProcCs     == TX_FIFO_FLUSH) ||
           abortTx_p                           ||
           (retryFrame_p && updateDMAStatus_p) ||
           trigNxtAtomFrm_p)
        abortTransaction    <= 1'b1;
      else if (transactionDone_p == 1'b1)
        abortTransaction    <=  1'b0;
    end
    else    
      abortTransaction    <= 1'b0;
        
  end
end

// handling the transaction size
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    transactionSize <= 16'd0;
  else if (macPITxClkSoftRst_n == 1'b0)
    transactionSize <= 16'd0;
  else
  begin
    case (txListProcCs)
      FETCH_HDR_DESC:  
        transactionSize <= `SIZE_TX_HDR_DESC;
      FETCH_PLD_DESC:  
        transactionSize <= `SIZE_TX_PLD_DESC;
      FETCH_PLY_TBL:   
        transactionSize <= `SIZE_TX_PLY_TBL;
      WR_DATA_TX_FIFO: 
        transactionSize <= bufLengthInQuads;
      UPDATE_PLD: 
        transactionSize <= 16'd1;
      IDLE:            
        transactionSize <= 16'd0;
      default:         
        transactionSize <= numQuadlets;
    endcase
  end
end

// manage the number of remaining data
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n) 
begin
  if (macPITxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    remainingData <= 16'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    remainingData <= 16'b0;
  end
  else
  begin
    if (abortTransaction == 1'b1)
      remainingData <= 16'b0;
    if (transactionEnable_p == 1'b1)
      remainingData <= transactionSize ;
    else if ((txListReadDataValid == 1'b1) && (remainingData != 16'b0))
      remainingData <= remainingData - 16'b1;
  end
end

// startburst management
// inidicate a burst is active
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n) 
begin
  if (macPITxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    ongoingBurst <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    ongoingBurst <= 1'b0;
  end
  else
  begin
    if (abortTransaction == 1'b1)
      ongoingBurst <= 1'b0;
    else
    begin
      // if the burst is completed
      if ( txListTransComplete  == 1'b1)
        ongoingBurst <= 1'b0;
      // if the burst is started
      else if (txListProcGrant == 1'b1)
        ongoingBurst <= 1'b1;
    end
  end 
end

assign  burstStart_p =  (ongoingTransaction &&           // start burst when we are in a transaction
                         !txFifoFull  &&                 // and the Tx FIFO is not full
                         (remainingData != 16'b0) &&     // and there are remaining data to be sent
                         !ongoingBurst) ? 1'b1 : 1'b0;   // and we are not already in a burst



always @*
begin
 // stop a burst only when one is started
 if (ongoingBurst == 1'b1)
 begin
   // when waitingTransEnd then the stoBurst has been asserted already 
   if (waitingTransEnd == 1'b0)
   begin
     // if a data is valid and Fifo is full or no remaining data to be transfered
     if ((txListReadDataValid == 1'b1) && ((txListLast == 1'b1) || (abortTransaction == 1'b1) || (suspendRead  == 1'b1) || (remainingData - 16'b1   == 16'b0)))
       burstStop_p = 1'b1;
     // otherwise
     else                           
       burstStop_p = 1'b0;
   end
   else
     burstStop_p = 1'b0;
 end
 else
   burstStop_p = 1'b0;
end


// indicate the read from the memory should be stopped 
// and no more data written to the FIFO
assign suspendRead = ( txListProcCs == WR_DATA_TX_FIFO_DONE &&                          // when data are moved to the FIFO
                     ( txFifoFull == 1'b1 || txFifoAlmostFull == 1'b1)) ? 1'b1 : 1'b0;  // and fifo is full or almost full

// handle tx list memory read
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n) 
begin
  if (macPITxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txListRead <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    txListRead <= 1'b0;
  end
  else
  begin
      if (txListProcGrant == 1'b1)   
      begin
        if (burstStart_p == 1'b1 && txListProcCs != WAIT_UPDATE_PLD_DONE)
          txListRead <= 1'b1;
        else if (burstStop_p == 1'b1)
          txListRead <= 1'b0;
      end
      else
        txListRead <= 1'b0;
  end    
end

// handle tx list memory read
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n) 
begin
  if (macPITxClkHardRst_n == 1'b0)  // Asynchronous Reset
    txListWrite <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)  // Synchronous Reset
    txListWrite <= 1'b0;
  else
  begin
    if (txListProcGrant == 1'b1)   
    begin
      if (ongoingTransaction == 1'b1 && !ongoingBurst && txListProcCs == WAIT_UPDATE_PLD_DONE)
        txListWrite <= 1'b1;
      else if (txListNextData == 1'b1)
        txListWrite <= 1'b0;
    end
    else
      txListWrite <= 1'b0;
  end    
end

assign txListSize = 3'b010;

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n) 
begin
  if (macPITxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    txListLast <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    txListLast <= 1'b0;
  end
  else
  begin
    // When there is a tx fifo flush or burst stop
    // Tehn reset the  txListLast Flag
    if((burstStop_p      == 1'b1) ||
       (abortTx_p        == 1'b1) ||
       (retryFrame_p     == 1'b1) ||
       (trigNxtAtomFrm_p == 1'b1)   )
    begin
      txListLast <= 1'b0;
    end
    else if((txListRead == 1'b1) && (txListReadDataValid == 1'b1) &&  (remainingData - 16'b1   <= 16'b1))
    begin
      txListLast <= 1'b1;
    end
  end
end



always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    usePldDesc <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    usePldDesc <= 1'b0;
  else if (txListProcCs == FETCH_PLD_DESC)
    usePldDesc <= 1'b1;
  else if ((txListProcCs == CHK_BUFFER_DESC_VALID) || (txListProcCs == IDLE))
    usePldDesc <= 1'b0;
end


//manage the txListStartAddress
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txListStartAddress <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txListStartAddress <= 32'b0;
  else
  begin
    case (txListProcCs)
      FETCH_HDR_DESC:
        txListStartAddress <= currentPtr;
      FETCH_PLD_DESC:
        txListStartAddress <= nxtPldBufDescPtr;
      WR_DATA_TX_FIFO:
        txListStartAddress <= dataStartPtr;
      WR_DATA_TX_FIFO_DONE:
        if (transactionEnable_p == 1'b1)
          txListStartAddress <= dataStartPtr;
        else if  (ongoingBurst == 1'b1 && txListTransComplete == 1'b1 )
          txListStartAddress <= dataStartPtr + {14'b0,quadletsRead,2'b0};
      FETCH_PLY_TBL:
        txListStartAddress <= polEntryAddr;
      UPDATE_PLD:
        txListStartAddress <= pldBufDescPtr + 32'd16;//(30`TX_PLD_BUF_STATUS << 2);
      default:
      begin
      end
    endcase
  end
end

assign txListWriteData = {1'b1,curStatusTPDValue[30:0]};

// manage access to the TxFIFO
always @*
begin
  if (txFifoFull)
    txFifoWr = 1'b0;
  else
    if (txListProcCs        == WR_DATA_TX_FIFO_DONE &&
        txListReadDataValid == 1'b1 )
      txFifoWr = 1'b1;
    else
      txFifoWr = 1'b0;
end

//Write signal to TX FIFO. Asserted only when the data is being 
//fetched from the SRAM.
assign txFifoWrData = (txFifoWr == 1'b1 ) ? txListReadData : 32'b0;

always @*
begin
  `ifndef RW_MPDU_AC
  if (( waitFirstDataWord == 1'b1 ) && (writeMH == 1'b1))
    txTagFifoWrData = {tagSelect, 4'b1100};
  else if (firstQuadlet && lastQuadlet)
  `else
  if (firstQuadlet && lastQuadlet)
  `endif
  // Handle the case where the dataStartPtr and dataEndPtr point on the same quadlet
  // In this case, the buffer length is less or equal to 4.
  begin
    if (dataStartPtr[1:0] == 2'b00) // buffer length = 4
      case (dataEndPtr[1:0])
        2'b00:  txTagFifoWrData = {tagSelect, 4'b0001}; 
        2'b01:  txTagFifoWrData = {tagSelect, 4'b0011};
        2'b10:  txTagFifoWrData = {tagSelect, 4'b0111};
        2'b11:  txTagFifoWrData = {tagSelect, 4'b1111};
      endcase
    else if (dataStartPtr[1:0] == 2'b01) // buffer length = 3
      case (dataEndPtr[1:0])
          2'b01:  txTagFifoWrData = {tagSelect, 4'b0010};
          2'b10:  txTagFifoWrData = {tagSelect, 4'b0110};
        default:  txTagFifoWrData = {tagSelect, 4'b1110};
      endcase
    else if (dataStartPtr[1:0] == 2'b10) // buffer length = 2
      case (dataEndPtr[1:0])
          2'b10:  txTagFifoWrData = {tagSelect, 4'b0100};
        default:  txTagFifoWrData = {tagSelect, 4'b1100};
      endcase
    else // buffer length = 1
      txTagFifoWrData = {tagSelect, 4'b1000};
  end
  `ifdef RW_MPDU_AC
  else if (firstQuadlet || (( waitFirstDataWord == 1'b1 ) && (writeMH == 1'b1)))
  `else
  else if (firstQuadlet)
  `endif
  // Handle the case where the dataStartPtr is not aligned
  begin
    case (dataStartPtr[1:0])
        2'b00:  txTagFifoWrData = {tagSelect, 4'b1111};
        2'b01:  txTagFifoWrData = {tagSelect, 4'b1110};
        2'b10:  txTagFifoWrData = {tagSelect, 4'b1100};
        2'b11:  txTagFifoWrData = {tagSelect, 4'b1000};
    endcase
  end
  else if (lastQuadlet)
  // Handle the case where the dataEndPtr is not aligned
  begin
    case (dataEndPtr[1:0])
        2'b00:  txTagFifoWrData = {tagSelect, 4'b0001};
        2'b01:  txTagFifoWrData = {tagSelect, 4'b0011};
        2'b10:  txTagFifoWrData = {tagSelect, 4'b0111};
        2'b11:  txTagFifoWrData = {tagSelect, 4'b1111};
    endcase
  end
  else
    txTagFifoWrData = {tagSelect, 4'b1111};
end


// End the handling of RAM And FIFO
////////////////////////////////////////////////////////


// Logic to generate the waitFirstDataWord
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    waitFirstDataWord <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    waitFirstDataWord <= 1'b0;
  else if (txListProcNs == WR_DATA_TX_FIFO_DONE &&
           txListProcCs == WR_DATA_TX_FIFO) 
    waitFirstDataWord <= 1'b1;
  else if (txFifoWr)
    waitFirstDataWord <= 1'b0;
end


//Logic for quadletsRead. This keeps a count of 
//number of quadlets read after every new transfer is started
//The indication given by the read write controller is used 
//to increment the counter by one
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    quadletsRead <= 16'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    quadletsRead <= 16'b0;
  else if ((txListProcCs == IDLE) ||
           (txListProcCs == UPD_CURR_PTR) ||
           (remainingData == 16'b0))
    quadletsRead <= 16'b0; 
  else if (((txListProcCs == WR_DATA_TX_FIFO_DONE) ||
            (txListProcCs == WAIT_FETCH_HDR_DESC_DONE) ||
            (txListProcCs == WAIT_FETCH_PLY_TBL_DONE) ||
            (txListProcCs == WAIT_FETCH_PLD_DESC_DONE)) &&
            txListReadDataValid)
    quadletsRead <= quadletsRead + 16'd1;
end

//Logic for numQuadlets
//This process assigns the number of quadlets remaining
//to be fetched for the transfer requested to be completed
//The size of the descriptors and policy table are fixed
//whereas the size of the buffer associated with header or
//payload is derived from the difference in the 
//dataStartPtr and the dataEndPtr
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    numQuadlets <= 16'd0;
  else if (macPITxClkSoftRst_n == 1'b0)
    numQuadlets <= 16'd0;
  else if (txListReadDataValid == 1'b1)
    numQuadlets <= numQuadlets - 16'b1;
  else
  begin
    case (txListProcCs)
      FETCH_HDR_DESC:  numQuadlets <= `SIZE_TX_HDR_DESC;
      FETCH_PLD_DESC:  numQuadlets <= `SIZE_TX_PLD_DESC;
      FETCH_PLY_TBL:   numQuadlets <= `SIZE_TX_PLY_TBL;
      WR_DATA_TX_FIFO: numQuadlets <= bufLengthInQuads;
      IDLE:            numQuadlets <= 16'd0;
      default:         numQuadlets <= numQuadlets;
    endcase
  end
end


//Logic for nxtAtomFrmPtr
//This shows the beginning header descriptor for the next
//frame exchange sequence
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    nxtAtomFrmPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    nxtAtomFrmPtr <= 32'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_NXT_ATOM_FRM_PTR - 1) &&
           txListReadDataValid)
    nxtAtomFrmPtr <= txListReadData;
end

//Logic for nxtMpduDescPtr;
//This shows the next Header descriptor pointer for the 
//next MPDU
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    nxtMpduDescPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    nxtMpduDescPtr <= 32'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_NXT_MPDU_DESC_PTR - 1) &&
           txListReadDataValid)
    nxtMpduDescPtr <= txListReadData;
end

//Logic for dataStartPtr
//Shows the starting location for the data associated with 
//this payload descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    dataStartPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    dataStartPtr <= 32'b0;
  else if ((((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
             (quadletsRead == `TX_HDR_BUF_START_PTR - 1)) ||
            ((txListProcCs == WAIT_FETCH_PLD_DESC_DONE) &&
             (quadletsRead == `TX_PLD_BUF_START_PTR - 1))) && 
             txListReadDataValid)
    dataStartPtr <= txListReadData;
end

// Set the flag dataStartPtrNull is the dataStartPtr is null
assign dataStartPtrNull = (dataStartPtr == 32'd0); 

////Logic for dataEndPtr
//Shows the ending location for the data associated with 
//this payload descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    dataEndPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    dataEndPtr <= 32'b0;
  else if ((((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
             (quadletsRead == `TX_HDR_BUF_END_PTR - 1)) ||
            ((txListProcCs == WAIT_FETCH_PLD_DESC_DONE) &&
             (quadletsRead == `TX_PLD_BUF_END_PTR - 1))) &&
             txListReadDataValid)
    dataEndPtr <= txListReadData;
end

//Gives the maximum lifetime this frame can be tried to
//be sent out. Obtained from the header descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    frameLifetime <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    frameLifetime <= 32'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_FRAME_LIFETIME - 1) &&
           txListReadDataValid)
    frameLifetime <= txListReadData;
end

//Address of the policy table. Obtained from the header
//descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    polEntryAddr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    polEntryAddr <= 32'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_PLY_ENTRY_ADDR - 1) &&
           txListReadDataValid)
    polEntryAddr <= txListReadData;
end

//Logic for descriptorDoneTx 
//Indicates if this descriptor has been already handled
//if yes then we go to the next descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    descriptorDoneTx     <=  1'b0;
    statusInformationReg <= 32'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    descriptorDoneTx     <=  1'b0;
    statusInformationReg <= 32'b0;
  end
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_STATUS_INFO - 1) &&
           txListReadDataValid)
  begin
    statusInformationReg <= txListReadData;
    descriptorDoneTx     <= txListReadData[31];
  end
end


//Logic fo nxtPldBufDescPtr
//Location of the next payload buffer descriptor pointer:
//The payload buffer descriptor pointer is present in 
//both the header descriptor and the payload descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    nxtPldBufDescPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    nxtPldBufDescPtr <= 32'b0;
  else if ((((txListProcCs == WAIT_FETCH_PLD_DESC_DONE) &&
             (quadletsRead == `TX_NXT_PLD_DESC_PTR - 1)) ||
            ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
             (quadletsRead == `TX_FIRST_PLD_DESC_PTR- 1))) &&
             txListReadDataValid)
    nxtPldBufDescPtr <= txListReadData;
end

always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    pldBufDescPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    pldBufDescPtr <= 32'b0;
  else if (txListProcCs == FETCH_PLD_DESC)
    pldBufDescPtr <= nxtPldBufDescPtr;
end


//Logic for currentPtr. 
//The current pointer is updated only in the UPD_CURR_PTR state.  
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    currentPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    currentPtr <= 32'b0;
  else if (txListProcCs == UPD_CURR_PTR)
  begin
  //Updation to next MPDU happens when the 
  //DMA is actively parsing an atomic frame 
  //exchange and there are still MPDU's 
  //remaining to be parsed in this exchange
    if (updNxtMpdu == 1'b1)
      currentPtr <= nxtMpduDescPtr;
  //Updation to next atomic frame exchange 
  //happens when the DMA is done with the 
  //atomic frame exchange and is going to 
  //start parsing a new atomic frame exchange
    else if (updNxtAtomFrm == 1'b1)
      currentPtr <= nxtAtomFrmPtr;
  //Incase the SW RTS frame is successful the 
  //status ptr will be pointing to that frame
  //when the subsequent frame is transmitted 
  //and is not successful and has to be retried
  //the currentPtr should not be updated 
    else if (prevFrmRts == 1'b1)
      currentPtr <= currentPtr;
  //Updation to the status pointer happens only
  //when the Primary controller is triggered 
  //to ACTIVE or when the frame is retried
    else
      currentPtr <= statusPointer;
  end
  else
    currentPtr <= currentPtr;
end


//Logic for updNxtAtomFrm.
//This flag indicates to update to the next atomic frame.
//This is asserted when the next buffer descriptor pointer 
//is not valid and the next MPDU descriptor pointer is not valid. 
//And in case of lifetimeExpired it does not check if the next
//mpdu descriptor is valid.  
//And in case of descriptorDoneTx being set it checks if the 
//whichDescriptor is equal to 00.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    updNxtAtomFrm <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    updNxtAtomFrm <= 1'b0;
  //in case of a MSDU fragment reaching the  
  //retryLimit the ptr is updated to next atomic 
  //frame pointer
  else if (trigNxtAtomFrm_p == 1'b1)
    updNxtAtomFrm <= 1'b1;
  else if (txListProcCs == PROC_HDR_DESC) 
  begin 
    if ((lifetimeExpired_p == 1'b1 ||
        (descriptorDoneTx == 1'b1 && 
         whichDesc == 2'b00)) && 
         nxtAtomFrmPtrValid == 1'b1) 
      updNxtAtomFrm <= 1'b1;
    else
      updNxtAtomFrm <= 1'b0;
  end
  else if (txListProcCs == CHK_BUFFER_DESC_VALID)
  begin
    if (!bufferValid_p &&
        !mpduValid_p &&
        atomicFrmValid_p)
      updNxtAtomFrm <= 1'b1;   
    else 
      updNxtAtomFrm <= 1'b0;     
  end
  else if (txListProcCs == UPD_CURR_PTR || 
           txListProcCs == ERROR ||
           txListProcCs == IDLE)
    updNxtAtomFrm <= 1'b0;
end

//Delay the trigNxtAtomFrm_p by a pulse to sense 
//in the TX_FIFO_FLUSH state
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigNxtAtomFrmReg_p <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigNxtAtomFrmReg_p <= 1'b0;
  else 
    trigNxtAtomFrmReg_p <= trigNxtAtomFrm_p;
end

//Logic for updNxtMpdu. 
//This flag indicates to update to the next MPDU. 
//This is asserted when the next Buffer Descriptor pointer
//is invalid and the next MPDU descriptor is valid
//After the policy table is processed if the frame is RTS
//or an AMPDU header descriptor then the updNxtMpdu is asserted 
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    updNxtMpdu <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    updNxtMpdu <= 1'b0;
  else if ((txListProcCs == UPD_CURR_PTR) ||
           (txListProcCs == ERROR) ||
           (txListProcCs == IDLE)  ||
           trigNxtAtomFrm_p)
    updNxtMpdu <= 1'b0;
  else if ((txListProcCs == PROC_HDR_DESC) &&
           (whichDesc != 2'b0) &&
           (nxtMpduDescValid == 1'b1) &&
           (descriptorDoneTx == 1'b1))
    updNxtMpdu <= 1'b1;
  else if (txListProcCs == CHK_BUFFER_DESC_VALID) 
  begin
    if (!bufferValid_p && mpduValid_p)
      updNxtMpdu <= 1'b1;
    else
      updNxtMpdu <= 1'b0;
  end
  else if (txListProcCs == PROC_PLY_TBL)
  begin
    if (ampduHdr && nxtMpduDescValid)
      updNxtMpdu <= 1'b1;
    else 
      updNxtMpdu <= 1'b0;
  end
end

//Logic for retryFrame
//This is used to retrigger the FSM to start fetching the 
//frame pointed by the status Pointer of the Primary 
//Controller
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    retryFrame <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    retryFrame <= 1'b0;
  else if (txListProcCs == UPD_CURR_PTR )
    retryFrame <= 1'b0;
  else if (retryFrame_p && updateDMAStatus_p)
    retryFrame <= 1'b1;
end

//Logic for interruptEnTx bit
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    interruptEnTx      <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    interruptEnTx      <= 1'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_MAC_CTRL2_INFO - 1) &&
           txListReadDataValid)
    interruptEnTx <= txListReadData[8];
end

//Logic for bufferInterruptEnTx bit
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    bufferInterruptEnTx      <= 1'b0;
    curStatusTPDValue        <= 32'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    bufferInterruptEnTx      <= 1'b0;
    curStatusTPDValue        <= 32'b0;
  end
  else if ((txListProcCs == WAIT_FETCH_PLD_DESC_DONE) &&
           (quadletsRead == `TX_PLD_BUF_STATUS - 1) &&
           txListReadDataValid)
  begin
    bufferInterruptEnTx      <= txListReadData[0];
    curStatusTPDValue        <= txListReadData;
  end
end

//Generate Tx Pld Descriptor Interrupt
assign bufferInterruptTx = (txListProcCs == WAIT_UPDATE_PLD_DONE) && transactionDone_p ? bufferInterruptEnTx : 1'b0;



//logic for ampduHdr
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ampduHdr <= 1'b0; 
  else if (macPITxClkSoftRst_n == 1'b0)
    ampduHdr <= 1'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_MAC_CTRL2_INFO - 1) &&
           txListReadDataValid)
    ampduHdr <=  txListReadData[21] &&
                ~txListReadData[20] &&
                ~txListReadData[19];
end

//logic for mac header generation
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    writeMH <= 1'b0; 
  else if (macPITxClkSoftRst_n == 1'b0)
    writeMH <= 1'b0;
  else if (txListProcCs == WAIT_FETCH_HDR_DESC_DONE)
    writeMH <=  1'b1;
  else if (txListProcCs == CHK_BUFFER_DESC_VALID)
    writeMH <=  1'b0;
end

//logic for ptFragment
// indicate Policy table has to be loaded
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ptFragment <= 1'b0; 
  else if (macPITxClkSoftRst_n == 1'b0)
    ptFragment <= 1'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_MAC_CTRL2_INFO - 1) &&
           txListReadDataValid)
    ptFragment <= ~txListReadData[21];
 else if (txListProcCs == IDLE)
    ptFragment <= 1'b0;
end

//Indicates to the status updater to store the 
//parameters of the THD . The parameters need not 
//be stored for AMPDU header descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    storeParameters_p <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    storeParameters_p <= 1'b0;
  else if ((txListProcCs == PROC_HDR_DESC) &&
           !(lifetimeExpired_p || nextFrameLifetimeExpired_p) &&
           !descriptorDoneTx &&
           ampduHdr == 1'b0)
    storeParameters_p <= 1'b1;
  else 
    storeParameters_p <= 1'b0;
end
//Indicates to the status updater to store the 
//parameters of the THD . The parameters need not 
//be stored for AMPDU header descriptor
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    storeAMPDUParameters_p <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    storeAMPDUParameters_p <= 1'b0;
  else if ((txListProcCs == PROC_HDR_DESC) &&
           !(lifetimeExpired_p || nextFrameLifetimeExpired_p) &&
           !descriptorDoneTx &&
           ampduHdr == 1'b1)
    storeAMPDUParameters_p <= 1'b1;
  else 
    storeAMPDUParameters_p <= 1'b0;
end

//Logic for whichDesc
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    whichDesc <= 2'd0;
  else if (macPITxClkSoftRst_n == 1'b0)
    whichDesc <= 2'd0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
           (quadletsRead == `TX_MAC_CTRL2_INFO - 1) &&
           txListReadDataValid)
    whichDesc <=  txListReadData[20:19];
end


//Logic for startMpdu.
//When the FSM enters the FETCH_HDR_DESC this signal
//is asserted. Only during the WR_DATA_TX_FIFO_DONE state
//the TAG FIFO is written. The first time the FSM reaches
//the WR_DATA_TX_FIFO_DONE state this signal is deasserted
//this ensures only for the first quadlets of the header 
//this indication is written
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    startMpdu <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    startMpdu <= 1'b0;
  else if ((txListProcCs == WR_DATA_TX_FIFO_DONE) &&
           txListReadDataValid)
    startMpdu <= 1'b0;
  else if (txListProcCs == FETCH_HDR_DESC)
    startMpdu <= 1'b1;
end

assign tagSelect = (startMpdu)? 2'b00 : ((endMpdu) ? 2'b10 : 2'b01);


always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    lifeTimeExpiredFlag <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    lifeTimeExpiredFlag <= 1'b0;
  else if ((staUpdTransComplete == 1'b1) && (lifeTimeExpiredFlag == 1'b1))
    lifeTimeExpiredFlag <= 1'b0;
  else if (lifetimeExpired_p == 1'b1)
    lifeTimeExpiredFlag <= 1'b1;
end



always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    nextFrameLifetimeExpiredFlag <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    nextFrameLifetimeExpiredFlag <= 1'b0;
  else if ((staUpdTransComplete == 1'b1) && (nextFrameLifetimeExpiredFlag == 1'b1))
    nextFrameLifetimeExpiredFlag <= 1'b0;
  else if (nextFrameLifetimeExpired_p == 1'b1)
    nextFrameLifetimeExpiredFlag <= 1'b1;
end

// Gating the lifetime expired if the header of mpdu inside ampdu is fetched or in case of BAR
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    lifetimeExpiredEn <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    lifetimeExpiredEn <= 1'b0;
  else if ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) && (quadletsRead == `TX_MAC_CTRL2_INFO - 1) && txListReadDataValid)
    lifetimeExpiredEn <= !((txListReadData[21] == 1'b1) ||      // Gating all ampdu header + mpdu  inside the ampdu 
                           (txListReadData[6:0] == 7'b1000011));// Gating BAR header
end

//Indicates when the fist quadlet is being processed
assign firstQuadlet = (numQuadlets == bufLengthInQuads) ? 1'b1 : 1'b0;

//Indicates when the last quadlet is being processed
assign lastQuadlet = (numQuadlets == 16'b1) ? 1'b1 : 1'b0;


//If the Pattern CAFEBABE is not found in the first field of the
//header descriptor or the pattern BADCABE1E is not foudn in the 
//first field of the policy table the patternError signal is generated 
always @*
begin
  if (txListReadDataValid  && quadletsRead == (`TX_UNIQUE_PATTERN - 1))
  begin
    case(txListProcCs)
      WAIT_FETCH_HDR_DESC_DONE:
        if (txListReadData != 32'hCAFEBABE)
          patternError_gen = 1'b1;
        else
          patternError_gen = 1'b0;
      WAIT_FETCH_PLD_DESC_DONE:
        if (txListReadData != 32'hCAFEFADE)
          patternError_gen = 1'b1;
        else
          patternError_gen = 1'b0;
      WAIT_FETCH_PLY_TBL_DONE:
        if (txListReadData != 32'hBADCAB1E)
          patternError_gen = 1'b1;
        else
          patternError_gen = 1'b0;
      default:
        patternError_gen = 1'b0;
    endcase      
  end
  else
  begin  
    patternError_gen = 1'b0;
  end
end

always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    patternError <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    patternError <= 1'b0;
  else 
    patternError <= patternError_gen;
end

//flush signal for the TX FIFO
assign txFIFOFlushDMA = (txListProcCs == TX_FIFO_FLUSH) ? 1'b1 : 1'b0;

//Validity of payload Buffer descriptor.
assign pldBufDescValid = ((nxtPldBufDescPtr[1:0] == 2'b00) && (nxtPldBufDescPtr != 32'b0)) ? 1'b1 : 1'b0;

//this signal shows that the current descriptor has expired its lifetime
assign lifetimeExpired_p = ( (txListProcCs       == PROC_HDR_DESC) &&
                             (noFrm2Update       ==  1'b1)         &&
                             (frameLifetime      != 32'b0)         &&
                             (descriptorDoneTx   ==  1'b0)         &&
                             (lifetimeExpiredEn  ==  1'b1)         &&
                             (frameLifetime - tsfTimerValue > 32'h80000000) ) ? 1'b1 : 1'b0;

assign nextFrameLifetimeExpired_p = (  (txListProcCs       == PROC_HDR_DESC) &&
                                       (noFrm2Update       ==  1'b0)         &&
                                       (frameLifetime      != 32'b0)         &&
                                       (descriptorDoneTx   ==  1'b0)         &&
                                       (lifetimeExpiredEn  ==  1'b1)         &&
                                       (frameLifetime - tsfTimerValue > 32'h80000000) ) ? 1'b1 : 1'b0;

//Asserted high if the txListReadDataValid Pointer is valid.
assign nxtMpduDescValid  = ((nxtMpduDescPtr[1:0] == 2'b00) && (nxtMpduDescPtr != 32'b0)) ? 1'b1 : 1'b0;

//Asserted HIGH if the next Atom Frame Exchange pointer is valid.
assign nxtAtomFrmPtrValid = ((nxtAtomFrmPtr[1:0] == 2'b00) && (nxtAtomFrmPtr != 32'b0)) ? 1'b1 : 1'b0;


//logic indicating a pointer is not aligned
assign pointerNotAligned = ( (nxtAtomFrmPtr[1:0]  != 2'b00) ||
                             (nxtMpduDescPtr[1:0] != 2'b00) || 
                             (nxtPldBufDescPtr[1:0]  != 2'b00)) ? 1'b1 : 1'b0;



//logic for bufferValid_p 
//indicates that the next buffer descriptor is valid
//When the transferDone_p occurs then it is possible
//that the payload fetched was associated with the header
//and it might be also possible that hte payload fetched
//was associated with a buffer descriptor. If the payload
//fetched was associated with the header descriptor then
//the firstPayloadBuffer decriptor validity has to be checked
//if the payload fetched was associated with hte buffer 
//descriptor then the nextBufferDescriptor validity has to 
//be checked
assign bufferValid_p =  ((txListProcCs == CHK_BUFFER_DESC_VALID) &&
                         pldBufDescValid) ? 1'b1 : 1'b0;
  
//logic for mpduValid_p.
//indicates that the next mpdu is valid.This signal
//has to occur at CHK_BUFFER_DESC_VALID state
assign mpduValid_p = ((txListProcCs == CHK_BUFFER_DESC_VALID) &&
                      nxtMpduDescValid) ? 1'b1 : 1'b0;
    
//logic for atomicFrmValid_p. 
//indicates that the next atomic frame exchange is valid.
//This signal has to occur at CHK_BUFFER_DESC_VALID state
assign atomicFrmValid_p = ((txListProcCs == CHK_BUFFER_DESC_VALID) &&
                           nxtAtomFrmPtrValid) ? 1'b1 : 1'b0;

//Logic for txCtrlRegWr
//This signal is a write signal to the txControl registers
//High when the txControl registers have to be populated
//Note that this signal is released when the readData from 
//the HI is not valid
assign txCtrlRegWr = (((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) &&
                      ((quadletsRead == `TX_LENGTH_INFO - 1) ||
                       (quadletsRead == `TX_PHY_CTRL_INFO - 1) ||
                     `ifndef RW_THD_V2
                       (quadletsRead == `TX_LENGTH_INFO_DROP20 - 1) ||
                       (quadletsRead == `TX_LENGTH_INFO_DROP40 - 1) ||
                       (quadletsRead == `TX_LENGTH_INFO_DROP80 - 1) ||
                     `endif // RW_THD_V2
                       (quadletsRead == `TX_MAC_CTRL1_INFO - 1) ||
                       (quadletsRead == `TX_MAC_CTRL2_INFO - 1) ||
                     `ifndef RW_THD_V2
                       (quadletsRead == `TX_MEDIUM_TIME_USED - 1) ||
                     `endif // RW_THD_V2
                       (quadletsRead == `TX_STATUS_INFO - 1))) ||
                      ((txListProcCs == WAIT_FETCH_PLY_TBL_DONE) &&
                      ((quadletsRead == `PLY_TBL_PHY_CTRL_INFO1  - 1) ||
                       (quadletsRead == `PLY_TBL_PHY_CTRL_INFO2  - 1) ||
                       (quadletsRead == `PLY_TBL_MAC_CTRL_INFO1  - 1) ||
                       (quadletsRead == `PLY_TBL_MAC_CTRL_INFO2  - 1) ||
                       (quadletsRead == `PLY_TBL_RATE_CTRL_INFO1 - 1) ||
                       (quadletsRead == `PLY_TBL_RATE_CTRL_INFO2 - 1) ||
                       (quadletsRead == `PLY_TBL_RATE_CTRL_INFO3 - 1) ||
                       (quadletsRead == `PLY_TBL_RATE_CTRL_INFO4 - 1) ||
                       (quadletsRead == `PLY_TBL_POWER_CTRL_INFO1 - 1) ||
                       (quadletsRead == `PLY_TBL_POWER_CTRL_INFO2 - 1) ||
                       (quadletsRead == `PLY_TBL_POWER_CTRL_INFO3 - 1) ||
                       (quadletsRead == `PLY_TBL_POWER_CTRL_INFO4 - 1) )) &&
                       txListReadDataValid) ? 
                       txListReadDataValid : 1'b0;

assign txCtrlRegHD = (txListProcCs == WAIT_FETCH_HDR_DESC_DONE) ?
                      1'b1 : 1'b0;

assign txCtrlRegPT = (txListProcCs == WAIT_FETCH_PLY_TBL_DONE) ?
                      1'b1 : 1'b0;

assign plyTblValid = ((polEntryAddr[1:0] == 2'b00) && (polEntryAddr != 32'b0)) ? 1'b1 : 1'b0;


//Logic for endMpdu
//This is an indication to the read write controller
//to write the status to the TAG fifo. 
//It is considered the end of MPDU when the next buffer 
//descriptor is not valid and the number of Quadlets to 
//be read has reached end of the current buffer length.
assign endMpdu = ((txListProcCs == WR_DATA_TX_FIFO_DONE) &&
                  (numQuadlets == 16'd1) &&
                  !pldBufDescValid) ? 1'b1: 1'b0;



//This signal instructs the TX Parameter Cache module 
//to discard the most recently fetched header descriptor
assign discardPrevHD_p = ((txListProcCs == DISCARD_PREV_HD) || ((txListProcCs == WAIT_FETCH_HDR_DESC_DONE) && (abortTx_p == 1'b1)))
                          ? 1'b1 : 1'b0;

//Logic for trigDead_p
//This signal triggers the Active Primary Controller
//fsm to go to DEAD state. This happens when there
//is an dmaHIF transaction ERROR
assign trigDead_p = (txListProcCs == ERROR) ? 1'b1 : 1'b0;

//Logic for trigHalt_p
//triggers the Active Primary controller FSM to HALTED state
assign trigHalt_p = (txListProcCs == RETURN_TO_IDLE) ? 1'b1 : 1'b0;

//Shifting the bufLength by 2 bits to divide it by 4.
//This is because the difference in the buffer start and
//end pointers will give a result in number of bytes. 
//This has to be converted to quadlets
assign bufLengthInQuads[15:0] = {2'b0,(dataEndPtr[15:2] - dataStartPtr[15:2]+ 14'b1)};


assign updStatusPtr_p = ((txListProcCs == TRIG_STATPTR_UPD) &&
                            (statusPointer == currentPtr)) ? 1'b1 : 1'b0;

assign statusPtr2Upd = (whichDesc == 2'b00 && nxtAtomFrmPtrValid == 1'b1) ?
                        nxtAtomFrmPtr : nxtMpduDescPtr;
 
 
assign txListProcIdle = (txListProcCs == IDLE) ? 1'b1 : 1'b0;
      
// Pulse indicating that the policy table pattern is not correct
assign ptError = ((txListProcCs == WAIT_FETCH_PLY_TBL_DONE) && patternError_gen) ? 1'b1 : 1'b0;

assign debugPortDMA3 = {abortTransaction,   // 15
                        ptFragment,         // 14
                        nxtMpduDescValid,   // 13
                        pldBufDescValid,    // 12
                        plyTblValid,        // 11
                        nxtAtomFrmPtrValid, // 10
                        patternError,       // 9
                        pointerNotAligned,  // 8
                        lifeTimeExpiredFlag,// 7
                        txListError,        // 6  
                        descriptorDoneTx,   // 5
                        txListProcCs};      // 4-0 5bits


assign debugPortDMA6 = {abortTx_p,
                        retryFrame_p,
                        trigNxtAtomFrm_p,
                        lifetimeExpired_p,
                        atomicFrmValid_p,
                        startMpdu,
                        storeParameters_p,
                        updNxtAtomFrm,
                        prevFrmRts,
                        transactionDone_p,
                        patternError_gen,
                        retryFrame,
                        updNxtMpdu,
                        suspendRead,
                        txListRead,
                        transactionEnable_p};

assign debugPortTxListA     = {txListProcCs[4:0],
                               remainingData[4:0],
                               transactionDone_p,
                               (~waitingTransEnd & ongoingBurst),
                               burstStart_p,
                               burstStop_p,
                               txListLast,
                               txListProcReq
                              };

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 
// rxPrimCtrl FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (txListProcCs)
     IDLE                     :  txListProcCs_str = {"IDLE"};
     CHK_MPDU_CNT             :  txListProcCs_str = {"CHK_MPDU_CNT"};
     UPD_CURR_PTR             :  txListProcCs_str = {"UPD_CURR_PTR"};
                                                    
                                                    
     FETCH_HDR_DESC           :  txListProcCs_str = {"FETCH_HDR_DESC"};
     WAIT_FETCH_HDR_DESC_DONE :  txListProcCs_str = {"WAIT_FETCH_HDR_DESC_DONE"};
     PROC_HDR_DESC            :  txListProcCs_str = {"PROC_HDR_DESC"};
     DISCARD_PREV_HD          :  txListProcCs_str = {"DISCARD_PREV_HD"};
     TRIG_STATPTR_UPD         :  txListProcCs_str = {"TRIG_STATPTR_UPD"};
     FETCH_PLY_TBL            :  txListProcCs_str = {"FETCH_PLY_TBL"};
     WAIT_FETCH_PLY_TBL_DONE  :  txListProcCs_str = {"WAIT_FETCH_PLY_TBL_DONE"};
     PROC_PLY_TBL             :  txListProcCs_str = {"PROC_PLY_TBL"};
     WR_DATA_TX_FIFO          :  txListProcCs_str = {"WR_DATA_TX_FIFO"};
     WR_DATA_TX_FIFO_DONE     :  txListProcCs_str = {"WR_DATA_TX_FIFO_DONE"};
     CHK_BUFFER_DESC_VALID    :  txListProcCs_str = {"CHK_BUFFER_DESC_VALID"};
     FETCH_PLD_DESC           :  txListProcCs_str = {"FETCH_PLD_DESC"};
     WAIT_FETCH_PLD_DESC_DONE :  txListProcCs_str = {"WAIT_FETCH_PLD_DESC_DONE"};
     WAIT_FOR_STATUS_UPDATE   :  txListProcCs_str = {"WAIT_FOR_STATUS_UPDATE"};
     TX_FIFO_FLUSH            :  txListProcCs_str = {"TX_FIFO_FLUSH"};
     UPDATE_PLD               :  txListProcCs_str = {"UPDATE_PLD"};
     WAIT_UPDATE_PLD_DONE     :  txListProcCs_str = {"WAIT_UPDATE_PLD_DONE"};
     ERROR                    :  txListProcCs_str = {"ERROR"};
                                                    
     RETURN_TO_IDLE           :  txListProcCs_str = {"RETURN_TO_IDLE"};
                     default  :  txListProcCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

`ifdef RW_ASSERT_ON

// Assertion Definitions
///////////////////////////

//$rw_sva Checks if the dataStartPtr is not greater than the dataEndPtr
property dataStartEndPtrCheck_prop;
@(posedge macPITxClk)
    ((firstQuadlet && lastQuadlet)) |->  dataEndPtr[1:0] >= dataStartPtr[1:0];
endproperty
dataStartEndPtrCheck: assert property (dataStartEndPtrCheck_prop); 

property errorCheck(inp1);
@(posedge macPITxClk) $rose(inp1) |=> trigDead_p;
endproperty

//$rw_sva Checks on pattern error the trigger to DEAD for a channel is asserted
patternErrorCheck: assert property(errorCheck(patternError));

//$rw_sva  Checks on bus error the trigger to DEAD for a channel is asserted
dmaHIFBusErrorCheck: assert property(errorCheck(txListError));

//$rw_sva Checks if the txParameters are not to be passed then discardPrevHD_p 
//signal is generated and in the next one clock cycle the txCtrlRegBusy 
//signal is brought down
property discardPrevParam1;
@(posedge macPITxClk)
    (lifetimeExpired_p) |=>
        discardPrevHD_p ##[0:1] !txCtrlRegBusy;
endproperty
discardTXparamCheck1: assert property (discardPrevParam1); 

//$rw_sva Checks if the policy table flush is correct
property policyTblFifoFlushCheck;
@(posedge macPITxClk) (!plyTblValid && txListProcCs == CHK_BUFFER_DESC_VALID) |=>
                     (txListProcCs == ERROR);
endproperty
policyTblFifoFlushCheck1: assert property(policyTblFifoFlushCheck);
`endif



endmodule