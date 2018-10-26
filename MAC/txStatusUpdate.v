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
// Dependencies     : 
// Description      :This module based on the indication given by the MAC 
//                   controller on the transmission of a frame will trigger 
//                   Read write controller to update the status information
//                   in the header descriptor for the transmitted frame
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
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module txStatusUpdater (
 
            //$port_g Clocks and Reset
            input  wire           macPITxClk,              // Port Definitions
            input  wire           macPITxClkHardRst_n,     // Hard Reset synchronized to Platform1 Clock - 80MHz
            input  wire           macPITxClkSoftRst_n,     // Soft Reset  synchronized to Platform1 Clock - 80MHz

            //$port_g Primary controllers interface 
            input  wire           ac0TrigTxListProc,       // Trigger for List Processor from AC0
            input  wire           ac1TrigTxListProc,       // Trigger for List Processor from AC1
            input  wire           ac2TrigTxListProc,       // Trigger for List Processor from AC2
            input  wire           ac3TrigTxListProc,       // Trigger for List Processor from AC3
            input  wire           bcnTrigTxListProc,       // Trigger for List Processor from Beacon
            input  wire    [ 3:0] whichDescriptorSW,       // Indicates the value of the partAMorMSDU field Controller
            //
            output wire           trigDeadBCNStaUpd_p,     // Trigger the TX primary controller to DEAD state
            output wire           trigDeadAC0StaUpd_p,     // Trigger the TX primary controller to DEAD state
            output wire           trigDeadAC1StaUpd_p,     // Trigger the TX primary controller to DEAD state
            output wire           trigDeadAC2StaUpd_p,     // Trigger the TX primary controller to DEAD state
            output wire           trigDeadAC3StaUpd_p,     // Trigger the TX primary controller to DEAD state
            output wire           updBcnStaPtr_p,          // Indication to the Beacon Primary Controller to udpate the status pointer
            output wire           updAc0StaPtr_p,          // Indication to the AC0 Primary Controller to udpate the status pointer
            output wire           updAc1StaPtr_p,          // Indication to the AC1 Primary Controller to udpate the status pointer
            output wire           updAc2StaPtr_p,          // Indication to the AC2 Primary Controller to udpate the status pointer
            output wire           updAc3StaPtr_p,          // Indication to the AC3 Primary Controller to udpate the status pointer
            output reg     [31:0] updateStatusPtr,         // Address to which the statusPointer of the Primary Controller has
                                                           // be updated.

            //$port_g Tx List processor interface
            input  wire    [31:0] statusPtr2Upd,           // StatusPtr to be updated to when the
                                                           // updStatusPtr_p is asserted. From LP
            input  wire           updStatusPtr_p,          // Trigger to updated the active channel status ptr
            input  wire           interruptEnTx,           // InterruptEnTx information from header descriptor
            input  wire           lifetimeExpired_p,       // The current MPDU being fetched has a lifetime expired. this is given by the
                                                           // transmit list processor to update the status with lifetime expired on the
                                                           // header descriptor.
            input  wire           storeParameters_p,       // Signal to store the parameters of the current MPDU the txList proc is
                                                           // fetching
            input  wire           storeAMPDUParameters_p,  // Signal to store the parameters of the current AMPDU the txList proc is
                                                           // fetching
            input  wire           retryLimitReached_p,     // Provided by the MAC Controller when the retry limit is reached for the MPDU
            input  wire    [31:0] statusPointer,           // Given by the Primary Controller. Points  to the header descriptor address for
                                                           // the currently transmitted MPDU except in the case of A-MPDU where it points
                                                           // to the header descriptor for the A-MPDU
            input  wire    [31:0] currentPtr,              // Given by Transmit List Processor. Shows the header descriptor address for the
            
            input  wire    [31:0] statusInformationReg,    // value of status information register
            input  wire    [31:0] nxtAtomFrmPtr,           // Indicates the next atomic frame exchange pointer from Transmit List Processor
            //
            output wire           mpduCtrFull,             // Indicates the Status updater has reached the maximum
                                                           // storage capability for transmit parameters
            output wire           prevFrmRts,              // Indicates the last transmitted frame was a SW prepared
                                                           // RTS frame
            output reg            trigNxtAtomFrm_p,        // Trigger to the transmit list proc to update to next
                                                           // atomic frame exchange pointer for retryLimitReached cases
            output wire           statusUpdated_p,         // Indicates the handling of the descriptor pointed by the status pointer
                                                           // is finished
            
            input  wire           txListProcIdle,          // Indicate the list processor is idle
            output wire           noFrm2Update,            // Indicates there are no more frames whose status is expected. Signal to
                                                           // Transmit List Processor
            input  wire           nxtMpduDescValid,        //Indicates the next MPDU Descriptor is valid
                                                           

            //$port_g MAC Controller interface
            input wire            updateDMAStatus_p,       // trigs the DMA Status update.
            
            input  wire           rtsSuccess_p,            // Issued by MAC Controller on successful transmission of RTS frame both
                                                           // HW formed and SW formed.
            input  wire           rtsFailed_p,             // Issued by MAC Controller when CTS is not received for transmission of RTS
                                                           // frame both HW formed and SW formed.
            input  wire           mpduSuccess_p,           // Issued by MAC COntroller when there is a successful transmission of a frame
            input  wire           mpduFailed_p,            // Issued by MAC Controller when the response for a transmitted frame is not
                                                           // received
            input  wire           retryFrame_p,            // If the transmitted frame has to be retried then this
                                                           // signal is asserted.

            input  wire           txMpduDone_p,            // Issued by MAC Controller after it has finished operating on a single
                                                           // constituent MPDU of the AMPDU
            input  wire    [ 1:0] transmissionBW,          // Issued by MAC Controller after it has transferred a MSDU or an AMPDU
            input  wire    [ 7:0] numMPDURetries,          // Maintained and given by MAC Controller. Valid when the trigger signals like
                                                           // mpduFailed_p/mpduSuccess_p occurs
            input  wire    [ 7:0] numRTSRetries,           // Maintained and given by MAC Controller. Valid when the trigger signals like
                                                           // rtsFailed_p/rtsSuccess_p occurs
            input  wire    [31:0] mediumTimeUsed,          // Indicates the medium Time Used for current transmission
                                                           // Valid when DMA status is being updated
            input  wire           swRTS_p,                 // Given by MAC Controller. Indicates if the current transmitted frame is a
                                                           // RTS frame formed by SW
            input  wire           ampduFrm_p,              // Given by MAC Controller. Indicates if the current transmitted frame is an
                                                           // AMPDU frame.

            //$port_g Tx Fifo interface
            input  wire           flushTxFifo,             // TX FIFO flush signal,

            //$port_g Tx Fifo interface
            output reg            txStaUpdaterReq,         // access to the bus granted
            //
            input  wire           txStaUpdaterGrant,       // access to the bus granted
            
            //$port_g rdWrCrtl interface
            output reg     [31:0] staUpdStartAddress,      // Starting Address from the system memory to read or write the data
            output reg            staUpdWrite,             // Write enable
            output reg     [31:0] staUpdWriteData,         // Written data
            //
            input  wire           staUpdError,             // Indicate a transfer error
            input  wire           staUpdNextData,          // Data written, push the next data        
            input  wire           staUpdTransComplete,     // transaction done

            output reg     [15:0] txStatusDebug,
            output wire    [15:0] debugPortDMATxStatus,

                    
            //$port_g interrupt controller
            output reg            tx0Trigger,              // Trigger for AC0 transmission interrupt
            output reg            tx1Trigger,              // Trigger for AC0 transmission interrupt
            output reg            tx2Trigger,              // Trigger for AC0 transmission interrupt
            output reg            tx3Trigger,              // Trigger for AC0 transmission interrupt
            output wire           bcnTrigger               // Trigger for AC0 transmission interrupt

            
            
         );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// txStatusUpdater FSM states definition
//$fsm_sd txStatusUpdater
localparam IDLE             = 3'd0,                        // Remains here until status update trigger
           TRANS_REQ        = 3'd1,                        // Request write transaction command to Rd Wr Ctlr
           WRITE_TX_STATUS  = 3'd2,                        // Send TX STATUS write command to Rd Wr Ctlr
           WRITE_MDM_TIME   = 3'd3,                        // Send Medium Time Used write command to Rd Wr Ctlr
           WAIT_TRANS_DONE  = 3'd4,                        // Wait for Rd Wr Ctlr to acknowledge transaction
           ERROR            = 3'd5;                        // In this state the Primary Controller is triggered to DEAD


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// String definition to display txPrimCtrlCs current state
reg   [16*8:0] txStatusUpdaterCs_str;
`endif // RW_SIMU_ON

reg            lifetimeExpiredFlag;                        // Registering the lifetimeExpired_p signal

reg            updateStatus;                               // Stores the update status indication

reg            interruptEnTxStored;                        // selects the interruptEnable bit for the curr
                                                           // descriptor
reg            ampduInterruptEnTxStored;                   // selects the interruptEnable bit for the curr
                                                           // descriptor
reg            descriptorDoneTxStored;                     // Stored value of descriptorDoneTx
reg            bcnTrigTxListProcStored;                    // Stores if the bcn channel was last active
reg            ac0TrigTxListProcStored;                    // Stores if the AC0 channel was last active
reg            ac1TrigTxListProcStored;                    // Stores if the AC1 channel was last active
reg            ac2TrigTxListProcStored;                    // Stores if the AC2 channel was last active
reg            ac3TrigTxListProcStored;                    // Stores if the AC3 channel was last active

reg            updStatusPtrReg_p;
reg      [2:0] txStatusUpdaterCs;                         // Current State register
reg      [2:0] txStatusUpdaterNs;                         // Next state register

reg     [31:0] statusInfoUp;                              // statusInfo to be updated in the status info
//reg     [31:0] storedRTSstatusInfoUp;                   // statusInfo to be written in stat info for RTS frm
reg      [1:0] mpduCtr;                                   // Counter holds the number of MPDUS for which
reg     [31:0] nextStatPtr;
reg     [31:0] currentStatPtr;
                                                          // the parameters are currently stored

wire           descriptorDoneHWTx_p;                      // descriptorDoneHWTx bit updated to this value
wire           trigDead_p;                                // Indicates the current state of FSM is in ERROR
wire           frmSuccessfulTx;                           // frmSuccessfulTx bit is updated to this value
wire           updateStatusInt_p;                         // is generated when the stat ptr has to be
                                                          // udpated
reg            ongoingAccess;                             // Indicates an access on the bus is performed

reg            txMpduDoneFlag;                            // Indicates the current update is for an ampdu intermediate mpdu
reg            firstStoreParameters;

reg            isAMPDUHeader;

wire           statusUpdateReq_p;                         // Pulse indicating that a status update has been requested from the MAC Core or
                                                          // a lifetime expired has been detected
reg [2:0]      txStatusDebugCnt;
reg [31:0]     txStatusDebugStatus;
reg [31:0]     txStatusDebugAddr;



reg [31:0]  nextNxtAtomFrmPtr;
reg         nextInterruptEnTx;
reg [31:0]  currentAMPDUStatPtr;
reg         ampduInterruptEnTx;
reg [31:0]  currentNxtAtomFrmPtr;
reg         currentInterruptEnTx;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign prevFrmRts = 1'b0;

//Current State logic 
always @(posedge macPITxClk or negedge macPITxClkHardRst_n )
begin : currentState
  if (macPITxClkHardRst_n == 1'b0)
     txStatusUpdaterCs <= IDLE;
   else if (macPITxClkSoftRst_n == 1'b0)
     txStatusUpdaterCs <= IDLE;
   else
     txStatusUpdaterCs <= txStatusUpdaterNs;
end


//Next State logic
always @*
begin : nextState
  case (txStatusUpdaterCs)
    IDLE: 
    //$fsm_s FSM waits in this state until a trigger for updation
    //of status information in the descriptor is received
    //This trigger is usually from the MAC Controller only.
    //Only the lifetimeExpired_p is from the txListProcessor
    begin
      if (statusUpdateReq_p)
        //$fsm_t When statusUpdateReq_p is received, the FSM moves to TRANS_TX_STATUS
        txStatusUpdaterNs = TRANS_REQ;
      else
        //$fsm_t While statusUpdateReq_p is not received, the FSM stays in IDLE
        txStatusUpdaterNs = IDLE;
    end

    TRANS_REQ:
    //$fsm_s In this state the FSM is waiting for access granted to the bus
    begin
      if(txStaUpdaterGrant)
        //$fsm_t The FSM moves to WRITE_TX_STATUS when txStaUpdaterGrant is received 
        txStatusUpdaterNs = WRITE_TX_STATUS;
      else
        //$fsm_t While txStaUpdaterGrant is not received, the FSM stays in TRANS_REQ
        txStatusUpdaterNs = TRANS_REQ;
    end
        
    WRITE_TX_STATUS:
    //$fsm_s In this state the FSM is sending a write command to Rd Wr Ctrl
    //to update TX Status in the header descriptor until staUpdNextData is received
    begin
      if (staUpdError == 1'b1)
        //$fsm_t If an error has been detected during the status update (staUpdError=1), 
        //the FSM moves to ERROR
        txStatusUpdaterNs = ERROR;
      if (staUpdNextData)
     `ifdef RW_THD_V2
        //$fsm_t The FSM moves to WAIT_TRANS_DONE when staUpdNextData is received 
        txStatusUpdaterNs = WAIT_TRANS_DONE;
     `else // RW_THD_V2
        //$fsm_t The FSM moves to WRITE_MDM_TIME when staUpdNextData is received 
        txStatusUpdaterNs = WRITE_MDM_TIME;
     `endif // RW_THD_V2
      else
        //$fsm_t While staUpdNextData is not received, the FSM stays in WRITE_TX_STATUS
        txStatusUpdaterNs = WRITE_TX_STATUS;
    end
      
    WRITE_MDM_TIME:
    //$fsm_s In this state the FSM is sending a write command to Rd Wr Ctrl
    //to update Medium Time Used in the header descriptor until staUpdNextData is received
    begin
      if (staUpdError == 1'b1)
        //$fsm_t If an error has been detected during the Medium Time Used update (staUpdError=1), 
        //the FSM moves to ERROR
        txStatusUpdaterNs = ERROR;
      else if (staUpdNextData)
        //$fsm_t The FSM moves to WAIT_TRANS_DONE when staUpdNextData is received 
        txStatusUpdaterNs = WAIT_TRANS_DONE;
      else
        //$fsm_t While staUpdNextData is not received, the FSM stays in WRITE_MDM_TIME
        txStatusUpdaterNs = WRITE_MDM_TIME;
    end
    
    WAIT_TRANS_DONE:
    //$fsm_s In this state the FSM waits until the request for the 
    //status updation is completed and a success response is 
    //received from the read write controller. 
    begin
      if (staUpdError == 1'b1)
        //$fsm_t If an error has been detected after sending write transaction (staUpdError=1), 
        //the FSM moves to ERROR
        txStatusUpdaterNs = ERROR;
      else if (staUpdTransComplete== 1'b1)
        //$fsm_t When the status update is completed (indicated by staUpdTransComplete), 
        //the FSM moves back to IDLE
        txStatusUpdaterNs = IDLE;
      else
        //$fsm_t While neither staUpdTransComplete or staUpdError is not received, the FSM stays in WAIT_STATUS_DONE
        txStatusUpdaterNs =  WAIT_TRANS_DONE;
    end 
  
    ERROR: 
     //$fsm_s In this state the FSM triggers the Primary Ctlr
     //to DEAD 

     //$fsm_t In this state the FSM triggers the Primary Ctlr
     //to DEAD 
      txStatusUpdaterNs = IDLE;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:
      txStatusUpdaterNs = IDLE;
    // pragma coverage block = on 
  endcase
end

assign statusUpdateReq_p = updateDMAStatus_p || lifetimeExpired_p || txMpduDoneFlag;



 
////////////////////////////////////////////////////////////////////
////
//// dmaHI Management
////
////////////////////////////////////////////////////////////////////



// handle the request to access the bus
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n )
begin
  if (macPITxClkHardRst_n == 1'b0)
    txStaUpdaterReq <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txStaUpdaterReq <= 1'b0;
  else
    if (txStatusUpdaterCs == TRANS_REQ)
      txStaUpdaterReq <= 1'b1; 
    else if (txStatusUpdaterCs == IDLE)
      txStaUpdaterReq <= 1'b0; 
end


//Logic for dmaHIFWrite logic
//This signal is used to request the Read Write Controller
//to write the statusInfo pointed to by the address pointer.
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n )
begin 
  if (macPITxClkHardRst_n == 1'b0) 
    staUpdWrite <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    staUpdWrite <= 1'b0;
  else
  begin
  `ifdef RW_THD_V2
    if ( (txStatusUpdaterCs == WRITE_TX_STATUS) && (staUpdNextData == 1'b1))
  `else // RW_THD_V2
    if ( (txStatusUpdaterCs == WRITE_MDM_TIME) && (staUpdNextData == 1'b1))
  `endif // RW_THD_V2
      staUpdWrite <= 1'b0;
    else if ((txStatusUpdaterCs == TRANS_REQ) &&
             (txStaUpdaterGrant == 1'b1) && (ongoingAccess == 1'b0))
      staUpdWrite <= 1'b1;
  end
end    

//$TODO Share adder
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    staUpdStartAddress <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    staUpdStartAddress <= 32'b0;
  else if (lifetimeExpiredFlag == 1'b1)
    staUpdStartAddress <= currentPtr + ((`TX_STATUS_INFO - 32'd1)<<32'd2);
  else if (ampduFrm_p)
    staUpdStartAddress <= currentAMPDUStatPtr + ((`TX_STATUS_INFO - 32'd1)<<32'd2);
  else if (updateDMAStatus_p || txMpduDone_p)  
    staUpdStartAddress <= currentStatPtr + ((`TX_STATUS_INFO - 32'd1)<<32'd2);
end


always @ (posedge macPITxClk or negedge macPITxClkHardRst_n )
begin 
  if (macPITxClkHardRst_n == 1'b0) 
    ongoingAccess <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    ongoingAccess <= 1'b0;
  else
  begin
    if (staUpdNextData == 1'b1)
      ongoingAccess <= 1'b1;
    else if (staUpdTransComplete ==  1'b1)
     ongoingAccess <= 1'b0;
  end
end    


//selection of statusInfoUp to be updated
always @*
begin
  case(txStatusUpdaterCs)
    WRITE_TX_STATUS : staUpdWriteData = statusInfoUp;
    WRITE_MDM_TIME  : staUpdWriteData = mediumTimeUsed;
    default         : staUpdWriteData = statusInfoUp;
  endcase
end


////////////////////////////////////////////////////////////////////
////
//// Header Descriptor Pointer Management
////
////////////////////////////////////////////////////////////////////

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    currentAMPDUStatPtr <= 32'd0;
    ampduInterruptEnTx  <= 1'b0;
    
  end  
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    currentAMPDUStatPtr <= 32'd0;
    ampduInterruptEnTx  <= 1'b0;
  end  
  else if (storeAMPDUParameters_p)
  begin
    currentAMPDUStatPtr <= currentPtr;
    ampduInterruptEnTx  <= interruptEnTx;
  end  
end

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    nextStatPtr       <= 32'd0;
    nextNxtAtomFrmPtr <= 32'd0;
    nextInterruptEnTx <= 1'b0;
    
  end  
  else if (macPITxClkSoftRst_n == 1'b0 || flushTxFifo == 1'b1) // Reset the all next register since the fifo is flushed and the next frame could be on another AC
  begin
    nextStatPtr       <= 32'd0;
    nextNxtAtomFrmPtr <= 32'd0;
    nextInterruptEnTx <= 1'b0;
  end  
  else if (!firstStoreParameters && storeParameters_p)
  begin
    nextStatPtr       <= currentPtr;
    nextNxtAtomFrmPtr <= nxtAtomFrmPtr;
    nextInterruptEnTx <= interruptEnTx;
  end  
end

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    currentStatPtr       <= 32'd0;
    currentNxtAtomFrmPtr <= 32'd0;
    currentInterruptEnTx <= 1'b0;
  end
  else if (macPITxClkSoftRst_n == 1'b0)
  begin
    currentStatPtr       <= 32'd0;
    currentNxtAtomFrmPtr <= 32'd0;
    currentInterruptEnTx <= 1'b0;
  end
  else if (firstStoreParameters && storeParameters_p)
  begin
    currentStatPtr       <= currentPtr;
    currentNxtAtomFrmPtr <= nxtAtomFrmPtr;
    currentInterruptEnTx <= interruptEnTx;
  end
  else if (statusUpdated_p && !retryFrame_p)
  begin
    currentStatPtr       <= nextStatPtr;
    currentNxtAtomFrmPtr <= nextNxtAtomFrmPtr;
    currentInterruptEnTx <= nextInterruptEnTx;
  end
end


// $TODO firstStoreParameters to be reset at the end of the TXOP
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    firstStoreParameters <= 1'd1;
  else if (macPITxClkSoftRst_n == 1'b0)
    firstStoreParameters <= 1'd1;
  else if (storeParameters_p == 1'b1)
    firstStoreParameters <= 1'd0;
  else if (txListProcIdle || storeAMPDUParameters_p)
    firstStoreParameters <= 1'd1;
end


////////////////////////////////////////////////////////////////////
////
//// Next Header Descriptor Pointer Management for txPrimary Controller
////
////////////////////////////////////////////////////////////////////


//Logic for updateStatusPtr 
//The pointer to which the status pointer in the Primary Controller
//is updated is chosen in this process. Unless its a successfully 
//transmitted A-MPDU frame  the pointer is updated to currentPointer else 
//it is updated to next Atomic Frame Exchange Descriptor.This is because
//in case of a successful transmission of the A-MPDU frame the 
//current pointer will be pointing towards the BAR frame which should
//be skipped in this case.
//This is assumed at the same time the lifetimeExpired_p doesnt
//arrive. 


always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    updateStatusPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    updateStatusPtr <= 32'b0;
  else if (updStatusPtr_p == 1'b1)
    updateStatusPtr <= statusPtr2Upd; 
  else if (lifetimeExpired_p)
  begin
    if(nextNxtAtomFrmPtr != 32'b0)
      updateStatusPtr <= nextNxtAtomFrmPtr;
    else
      updateStatusPtr <= currentPtr;
  end
  else if (updateDMAStatus_p == 1'b1)
  begin
    if (retryFrame_p)
    begin
      if (ampduFrm_p)
        updateStatusPtr <= currentAMPDUStatPtr;
      else
        updateStatusPtr <= currentStatPtr;
    end
    else
    begin    
      if (ampduFrm_p)
      begin
        if(retryLimitReached_p)
          updateStatusPtr <= currentAMPDUStatPtr;
        else
          updateStatusPtr <= currentStatPtr;
      end
      //check for validity of next atomic frame exchange pointer
      else if ((currentNxtAtomFrmPtr[1:0] == 2'b00) && (currentNxtAtomFrmPtr != 32'b0))
        updateStatusPtr <= currentNxtAtomFrmPtr;
      else  
        updateStatusPtr <= currentStatPtr;
    end    
  end    
end

//signal to the Primary Controller to update the status pointer
assign updateStatusInt_p = updateDMAStatus_p || lifetimeExpired_p;

////////////////////////////////////////////////////////////////////
////
//// statusInfoUp Management
////
////////////////////////////////////////////////////////////////////


//statusInfoUp Preparation
//The statusInfoUp to be updated as status information is 
//prepared.
//The descriptorDoneSWTx_p bit is set to zero because the
//HW will not pass a frame with that bit set to one
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    statusInfoUp <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    statusInfoUp <= 32'b0;
  else if ( lifetimeExpired_p == 1'b1 )
    statusInfoUp <= {descriptorDoneHWTx_p, 1'b0, 
                whichDescriptorSW,  
                8'b0, 
                1'b1,
                17'b0} | statusInformationReg;
  else if (statusUpdateReq_p)
  begin
    if (ampduFrm_p)
      // In case of AMPDUHeader descriptor status update, the two LSB of whichDescriptorSW are forced to 1
      statusInfoUp <= {descriptorDoneHWTx_p, 1'b0, 
                  whichDescriptorSW[3:2],2'b00, transmissionBW, !retryFrame_p, 
                  5'b0, lifetimeExpired_p,
                  retryLimitReached_p, numMPDURetries,
                  numRTSRetries
                 };
    else             
      statusInfoUp <= {descriptorDoneHWTx_p, 1'b0, 
                  whichDescriptorSW, transmissionBW, frmSuccessfulTx, 
                  5'b0, lifetimeExpired_p,
                  retryLimitReached_p, numMPDURetries,
                  numRTSRetries
                 };
  end               
end

////Stored RTS statusInfoUp
////Stores the statusInfoUp of SW formed RTS frame to be written
////when the subsequent MPDU is transmitted successfully.
//always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
//begin
//  if (macPITxClkHardRst_n == 1'b0)
//    storedRTSstatusInfoUp <= 32'b0;
//  else if (macPITxClkSoftRst_n == 1'b0)
//    storedRTSstatusInfoUp <= 32'b0;
//  else if (updateDMAStatus_p && rtsSuccess_p && swRTS_p)
//    storedRTSstatusInfoUp <= {descriptorDoneHWTx_p, 1'b0,
//                         4'b0, transmissionBW, frmSuccessfulTx, 
//                         11'b0, lifetimeExpired_p,  
//                         retryLimitReached_p, 3'b0, numMPDURetries,    
//                         numRTSRetries 
//                        };
//  else if (updateDMAStatus_p && mpduSuccess_p)
//    storedRTSstatusInfoUp <= {mpduSuccess_p, storedRTSstatusInfoUp[30:0]};
//end





//This signal triggers the TX List processor to FLUSH
//the FIFO and move to the next atomic frame exchange 
//pointer if the retry limit is reached for a middle
//or starting fragment in a fragment burst.
//If the retry limit is reached for the last fragment
//then it is not a problem because the next packet
//from the next atomic frame exchange sequence would
//have been fetched and kept in the FIFO
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigNxtAtomFrm_p <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigNxtAtomFrm_p <= 1'b0;
  else if ((retryLimitReached_p == 1'b1) &&
          ((whichDescriptorSW[0] == 1'b1) ||
           (whichDescriptorSW[1] == 1'b1)))
    trigNxtAtomFrm_p <= 1'b1;
  else
    trigNxtAtomFrm_p <= 1'b0;   
end


//This counter keeps in track number of MPDU's
//in FIFO. This makes sure the parameters stored
//locally do not get overwritten.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    mpduCtr <= 2'd0;
  else if (macPITxClkSoftRst_n == 1'b0)
    mpduCtr <= 2'd0; 
  else if (flushTxFifo == 1'b1)
    mpduCtr <= 2'd0;
  else if ((mpduCtr != 2'b00) && (updateStatusInt_p || (txMpduDone_p && (whichDescriptorSW[1:0] != 2'd3))))
  begin
    if (storeParameters_p == 1'b1)
      // If updateStatusInt_p and storeParameters_p occurs at the same time, 
      // mpduCtr shall not be changed
      mpduCtr <= mpduCtr;
    else
      mpduCtr <= mpduCtr - 2'd1;
  end    
  else if (storeParameters_p == 1'b1)
    mpduCtr <= mpduCtr + 2'd1;
end


  
//This holds the update status indication till the 
//descriptor updation has been done.
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    updateStatus <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    updateStatus <= 1'b0;
  else if (updateStatusInt_p == 1'b1)
    updateStatus <= 1'b1;
  else if (staUpdTransComplete== 1'b1)
    updateStatus <= 1'b0;
end






//Stores the interruptEnTx bit information of the 
//currently transmitted packet. When the indication is
//given for the successful or unsuccessful transmission
//the status of the interruptEnTx bit is captured.
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    interruptEnTxStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    interruptEnTxStored <= 1'b0;
  else if (descriptorDoneHWTx_p)
    interruptEnTxStored <= currentInterruptEnTx;
end

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ampduInterruptEnTxStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    ampduInterruptEnTxStored <= 1'b0;
  else if (ampduFrm_p && descriptorDoneHWTx_p)
    ampduInterruptEnTxStored <= ampduInterruptEnTx;
end



//If the beacon was the last active channel that information
//is stored still the descriptor done is updated and the 
//beacon primary controller status pointer is updated
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    bcnTrigTxListProcStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    bcnTrigTxListProcStored <= 1'b0;
  else if (bcnTrigTxListProc == 1'b1)
    bcnTrigTxListProcStored <= 1'b1;
  else if ((updateStatusInt_p == 1'b1) || (mpduCtr == 2'b0))
    bcnTrigTxListProcStored <= 1'b0;
end

//If the AC0 was the last active channel that information
//is stored still the descriptor done is updated and the 
//AC0 primary controller status pointer is updated
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ac0TrigTxListProcStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    ac0TrigTxListProcStored <= 1'b0;
  else if (ac0TrigTxListProc == 1'b1)
    ac0TrigTxListProcStored <= 1'b1;
  else if ((updateStatusInt_p == 1'b1) || (mpduCtr == 2'b0))
    ac0TrigTxListProcStored <= 1'b0;
end

//If the AC1 was the last active channel that information
//is stored still the descriptor done is updated and the 
//AC1 primary controller status pointer is updated
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ac1TrigTxListProcStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    ac1TrigTxListProcStored <= 1'b0;
  else if (ac1TrigTxListProc == 1'b1)
    ac1TrigTxListProcStored <= 1'b1;
  else if ((updateStatusInt_p == 1'b1) || (mpduCtr == 2'b0))
    ac1TrigTxListProcStored <= 1'b0;
end

//If the AC2 was the last active channel that information
//is stored still the descriptor done is updated and the 
//AC2 primary controller status pointer is updated
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ac2TrigTxListProcStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    ac2TrigTxListProcStored <= 1'b0;
  else if (ac2TrigTxListProc == 1'b1)
    ac2TrigTxListProcStored <= 1'b1;
  else if ((updateStatusInt_p == 1'b1) || (mpduCtr == 2'b0))
    ac2TrigTxListProcStored <= 1'b0;
end

//If the AC3 was the last active channel that information
//is stored still the descriptor done is updated and the 
//AC3 primary controller status pointer is updated
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    ac3TrigTxListProcStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    ac3TrigTxListProcStored <= 1'b0;
  else if (ac3TrigTxListProc == 1'b1)
    ac3TrigTxListProcStored <= 1'b1;
  else if ((updateStatusInt_p == 1'b1) || (mpduCtr == 2'b0))
    ac3TrigTxListProcStored <= 1'b0;
end

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    lifetimeExpiredFlag <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    lifetimeExpiredFlag <= 1'b0;
  else if (lifetimeExpired_p == 1'b1)
    lifetimeExpiredFlag <= 1'b1;
  else if (txStatusUpdaterCs == IDLE)
    lifetimeExpiredFlag <= 1'b0;
end

always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    descriptorDoneTxStored <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    descriptorDoneTxStored <= 1'b0;
  else if (txStatusUpdaterCs == IDLE)
    descriptorDoneTxStored <= descriptorDoneHWTx_p;
  else if (staUpdTransComplete == 1'b1)
    descriptorDoneTxStored <= 1'b0;
end

//Delayed version of updStatusPtr_p
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    updStatusPtrReg_p <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    updStatusPtrReg_p <= 1'b0;
  else 
    updStatusPtrReg_p <= updStatusPtr_p;
end 
    
//
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txMpduDoneFlag <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txMpduDoneFlag <= 1'b0;
  else 
  begin  
     if (txMpduDone_p)
       txMpduDoneFlag <= 1'b1;
    else if (staUpdTransComplete == 1'b1)
      txMpduDoneFlag <= 1'b0;
  end
end 


always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    isAMPDUHeader <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    isAMPDUHeader <= 1'b0;
  else if (ampduFrm_p)
    isAMPDUHeader <= 1'b1;
  else if (staUpdTransComplete)
    isAMPDUHeader <= 1'b0;
end


//Logic for descriptorDoneTx
//This signal is set when mpduSuccess_p or retryLimitReached or 
//lifetimeExpired_p  occurs. Also when A-MPDU transmission fails
//as indicated by ampduFrm == 1'b1 && mpduFailed_p == 1'b1

assign descriptorDoneHWTx_p =  (updateDMAStatus_p && !retryFrame_p) ||
                               lifetimeExpired_p ||
                               txMpduDoneFlag;




//Transmission trigger interrupt for AC0 if the descriptor done bit is
//set
//assign tx0Trigger = ((lifetimeExpiredFlag) ? interruptEnTx : interruptEnTxStored)
//                     && staUpdTransComplete && ac0TrigTxListProcStored &&
//                       descriptorDoneTxStored;                    

always @*
begin
  if (staUpdTransComplete && ac0TrigTxListProcStored &&  descriptorDoneTxStored)
  begin
    if (lifetimeExpiredFlag)
      tx0Trigger = interruptEnTx;
    else if (isAMPDUHeader)	
      tx0Trigger = ampduInterruptEnTxStored;
    else
      tx0Trigger = interruptEnTxStored;
  end
  else
    tx0Trigger = 1'b0;
end


//Transmission trigger interrupt for AC1 if the descriptor done bit is
//set
//assign tx1Trigger = ((lifetimeExpiredFlag) ? interruptEnTx : interruptEnTxStored)
//                     && staUpdTransComplete && ac1TrigTxListProcStored &&
//                       descriptorDoneTxStored;
always @*
begin
  if (staUpdTransComplete && ac1TrigTxListProcStored &&  descriptorDoneTxStored)
  begin
    if (lifetimeExpiredFlag)
      tx1Trigger = interruptEnTx;
    else  if (isAMPDUHeader)	
      tx1Trigger = ampduInterruptEnTxStored;
    else
      tx1Trigger = interruptEnTxStored;
  end
  else
    tx1Trigger = 1'b0;
end

//Transmission trigger interrupt for AC2 if the descriptor done bit is
//set
//assign tx2Trigger = ((lifetimeExpiredFlag) ? interruptEnTx : interruptEnTxStored)
//                     && staUpdTransComplete && ac2TrigTxListProcStored &&
//                       descriptorDoneTxStored;
always @*
begin
  if (staUpdTransComplete && ac2TrigTxListProcStored &&  descriptorDoneTxStored)
  begin
    if (lifetimeExpiredFlag)
      tx2Trigger = interruptEnTx;
    else  if (isAMPDUHeader)	
      tx2Trigger = ampduInterruptEnTxStored;
    else
      tx2Trigger = interruptEnTxStored;
  end
  else
    tx2Trigger = 1'b0;
end
//Transmission trigger interrupt for AC3 if the descriptor done bit is
//set
//assign tx3Trigger = ((lifetimeExpiredFlag) ? interruptEnTx : interruptEnTxStored)
//                     && staUpdTransComplete && ac3TrigTxListProcStored &&
//                       descriptorDoneTxStored;
always @*
begin
  if (staUpdTransComplete && ac3TrigTxListProcStored &&  descriptorDoneTxStored)
  begin
    if (lifetimeExpiredFlag)
      tx3Trigger = interruptEnTx;
    else  if (isAMPDUHeader)	
      tx3Trigger = ampduInterruptEnTxStored;
    else
      tx3Trigger = interruptEnTxStored;
  end
  else
    tx3Trigger = 1'b0;
end

//Transmission trigger interrupt for Beacon if the descriptor done bit is
//set
assign bcnTrigger = ((lifetimeExpiredFlag) ? interruptEnTx : interruptEnTxStored) 
                     && staUpdTransComplete && bcnTrigTxListProcStored &&
                       descriptorDoneTxStored;

//Set when there is a successful transmission of SW formed frames
// assign frmSuccessfulTx =  (rtsSuccess_p && swRTS_p) || mpduSuccess_p || txMpduDoneFlag ||
//                           (ampduFrm_p && mpduSuccess_p);
assign frmSuccessfulTx =  (updateDMAStatus_p && ((rtsSuccess_p && swRTS_p) || mpduSuccess_p)) || txMpduDoneFlag;


//Status Pointer updation indication for the beacon channel. Generated when 
//the last triggered channel was for Beacon and when transmission of a packet
//is successful as indicated by the updateStatus signal and the descriptor is
//updated successfully as indicated by the staUpdNextData signal
assign updBcnStaPtr_p = (updateStatus && staUpdTransComplete &&
                               bcnTrigTxListProcStored) ||
                              (updStatusPtrReg_p && bcnTrigTxListProc);

//Status Pointer updation indication for the AC0 channel. Generated when 
//the last triggered channel was for AC0 and when transmission of a packet
//is successful as indicated by the updateStatus signal and the descriptor is
//updated successfully as indicated by the staUpdNextData signal
assign updAc0StaPtr_p = (updateStatus && staUpdTransComplete &&
                               ac0TrigTxListProcStored) ||
                              (updStatusPtrReg_p && ac0TrigTxListProc);

//Status Pointer updation indication for the AC1 channel. Generated when 
//the last triggered channel was for AC1 and when transmission of a packet
//is successful as indicated by the updateStatus signal and the descriptor is
//updated successfully as indicated by the staUpdNextData signal
assign updAc1StaPtr_p = (updateStatus && staUpdTransComplete &&
                               ac1TrigTxListProcStored) ||
                              (updStatusPtrReg_p && ac1TrigTxListProc);

//Status Pointer updation indication for the AC2 channel. Generated when 
//the last triggered channel was for AC2 and when transmission of a packet
//is successful as indicated by the updateStatus signal and the descriptor is
//updated successfully as indicated by the staUpdNextData signal
assign updAc2StaPtr_p = (updateStatus && staUpdTransComplete &&
                               ac2TrigTxListProcStored) ||
                              (updStatusPtrReg_p && ac2TrigTxListProc);

//Status Pointer updation indication for the AC3 channel. Generated when 
//the last triggered channel was for AC3 and when transmission of a packet
//is successful as indicated by the updateStatus signal and the descriptor is
//updated successfully as indicated by the staUpdNextData signal
assign updAc3StaPtr_p = (updateStatus && staUpdTransComplete &&
                               ac3TrigTxListProcStored) ||
                              (updStatusPtrReg_p && ac3TrigTxListProc);

//Triggering the primary controller to DEAD
assign trigDead_p = (txStatusUpdaterCs == ERROR)  ? 1'b1: 1'b0;

//Triggering the BCN channel to DEAD if it was last active
assign trigDeadBCNStaUpd_p = trigDead_p && bcnTrigTxListProcStored;

//Triggering the AC0 channel to DEAD if it was last active
assign trigDeadAC0StaUpd_p = trigDead_p && ac0TrigTxListProcStored;

//Triggering the AC1 channel to DEAD if it was last active
assign trigDeadAC1StaUpd_p = trigDead_p && ac1TrigTxListProcStored;

//Triggering the AC2 channel to DEAD if it was last active
assign trigDeadAC2StaUpd_p = trigDead_p && ac2TrigTxListProcStored;

//Triggering the AC3 channel to DEAD if it was last active
assign trigDeadAC3StaUpd_p = trigDead_p && ac3TrigTxListProcStored;

//Indicates there are 2 frames currently fetched and no more frames
//can be fetched yet
assign mpduCtrFull = (mpduCtr == 2'd2) ? 1'b1 : 1'b0;


//Indicates the status is updated for the currently expected frame. In case of RTS
//followed by MPDU transmission the signal is generated after the both the MPDU and
//the RTS status are updated. Hence checking for retrigger signal being low.
//assign statusUpdated_p = (~retriggerDelayed && staUpdTransComplete) || retryFrame_p || swRTS_p;
//assign statusUpdated_p = (~retriggerDelayed && staUpdTransComplete);
assign statusUpdated_p = (staUpdTransComplete);

//This indicates there are no more frames whose status is expected 
assign noFrm2Update = ((mpduCtr == 2'b00) && (txStatusUpdaterCs == IDLE)) ? 
                        1'b1 : 1'b0;



////////////////////////////////////////////////////////////////////////////////
// Debug Interface
////////////////////////////////////////////////////////////////////////////////

                        
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    txStatusDebug    <= 16'b0;
    txStatusDebugCnt <= 3'd0;
  end
  else if (staUpdWrite && (txStatusDebugCnt == 3'd0))
  begin
    txStatusDebug    <= staUpdStartAddress[31:16];
    txStatusDebugCnt <= 3'd1;
  end
  else if (txStatusDebugCnt == 3'd1) 
  begin
    txStatusDebug    <= txStatusDebugAddr[15:0];
    txStatusDebugCnt <= 3'd2;
  end
  else if (txStatusDebugCnt == 3'd2) 
  begin
    txStatusDebug    <= txStatusDebugStatus[31:16];
    txStatusDebugCnt <= 3'd3;
  end
  else if (txStatusDebugCnt == 3'd3) 
  begin
    txStatusDebug    <= txStatusDebugStatus[15:0];
    txStatusDebugCnt <= 3'd4;
  end
  else if (txStatusDebugCnt == 3'd4) 
  begin
    txStatusDebug    <= 16'hffff;
    txStatusDebugCnt <= 3'd0;
  end
end

always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
  begin
    txStatusDebugStatus <= 32'b0;
    txStatusDebugAddr  <= 32'b0;
  end
  else if (staUpdWrite)
  begin
    txStatusDebugAddr   <= staUpdStartAddress;
    txStatusDebugStatus <= staUpdWriteData;
  end  
end

assign debugPortDMATxStatus = {storeParameters_p || txListProcIdle,
                              lifetimeExpired_p,
                              updateDMAStatus_p,
                              updStatusPtr_p,
                              descriptorDoneHWTx_p,
                              retryFrame_p,
                              mpduSuccess_p,
                              retryLimitReached_p,
                              statusUpdateReq_p,
                              updateStatusPtr[14:8]};


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////                  
                        
`ifdef RW_SIMU_ON
// pragma coverage block = off 
// txStatusUpdater FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (txStatusUpdaterCs)
     IDLE                       :  txStatusUpdaterCs_str = {"IDLE"};
     TRANS_REQ                  :  txStatusUpdaterCs_str = {"TRANS_REQ"};
     WRITE_TX_STATUS            :  txStatusUpdaterCs_str = {"WRITE_TX_STATUS"};
     WRITE_MDM_TIME             :  txStatusUpdaterCs_str = {"WRITE_MDM_TIME"};
     WAIT_TRANS_DONE            :  txStatusUpdaterCs_str = {"WAIT_TRANS_DONE"};
     ERROR                      :  txStatusUpdaterCs_str = {"ERROR"};
     default                    :  txStatusUpdaterCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON


endmodule
