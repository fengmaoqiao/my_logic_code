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
// Description      : This module takes care of initiating and controllign the
//                    movement of the received frame in the RX FIFO to the 
//                    Local SRAM. It instructs teh Read Write Controller on the
//                    necessary actions to be taken like fetching the header
//                    descriptor payload descriptor and moving the header adn 
//                    the payload from teh FIFO to teh local SRAM
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
//////////////////////////////////////////////////////////////////////////////
`include "commonDefines.v"
`include "commonDefine.v"


`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module rxListProc (

        //$port_g Clocks and Reset        
        input wire         macPIRxClk,                  // Clock synchronized to Platform2 domain
        input wire         macPIRxClkHardRst_n,         // Hard Reset synchronized to macPIRxClk
        input wire         macPIRxClkSoftRst_n,         // Soft Reset synchronized to macPIRxClk


        //$port_g rxFifo interface
        output reg         rxFifoRd,                    //  Fifo Read access indicator
        //
        input  wire        rxFifoEmpty,                 // FIFO empty indication
        input  wire        rxFifoAlmEmpty,              // FIFO alsmost empty indication
        input  wire [ 3:0] rxTagFifoRdData,             // output wire from the RX TAG FIFO
        input  wire [31:0] rxFifoRdData,                // Data read from RX FIFO

        //$port_g RdWrCtrl interface
        output reg  [31:0] rxListStartAddress,          // Starting Address from the system memory to read or write the data
        output reg         rxListRead,                  // Read enable
        output reg         rxListWrite,                 // Write enable
        output wire [ 2:0] rxListSize,                  // Access size
        output reg  [31:0] rxListWriteData,             // Written data
        output reg         rxListLast,                  // One more acces and end the burst
        //
        input  wire        rxListError,                 // Indicate a transfer error
        input  wire        rxListNextData,              // Data written, push the next data        
        input  wire [31:0] rxListReadData,              // Read data
        input  wire        rxListReadDataValid,         // Read data Valid
        input  wire        rxListTransComplete,         // transaction done

        //$port_g DMA arbitrer interface
        output reg         rxListProcReq,               // Receive List Processor request for grant from arbiter
        //          
        input  wire        rxListProcGrant,             // Grant for the recieve list processor
        
        //$port_g Header Primary controller interface
        input  wire [31:0] hdrStatusPointer,            // Status Pointer for the header channel
        input  wire [ 3:0] rxHeaderState,               // Current state of Header Primary Controller
        input  wire [ 3:0] rxPayloadState,              // Current state of Payload Primary Controller
        input  wire        rxHeaderNewTail,             // New tail for rx header Primary Controller
        input  wire        rxPayloadNewTail,            // New tail for rx payload Primary Controller
        //
        output wire        trigHdrPassive_p,            // Triggers the Header Primary Controller FSM to PASSIVE
        output wire        trigHdrHalt_p,               // Triggers the Header Primary Controller FSM to HALTED
        output wire        trigHdrActive_p,             // Triggers the Header Primary Controller FSM to ACTIVE
        output wire        trigHdrDead_p,               // Triggers the Header Primary Controller FSM to DEAD
        output wire        updHdrStaPtr_p,              // Updates the status pointer of the header primary controler
        output reg  [31:0] nxtHdrDescPtr,               // The address to which the status pointer of the header channel
                                                        // should be updated to
        output reg         rxHdrUPatternErr,            // Receive Header Unique Pattern Error
        output reg         rxHdrBusErr,                 // Receive Header Bus Error
        output reg         rxHdrNextPointerErr,         // Receive Header Next Pointer Error
        
        //$port_g Payload Primary controller interface
        input  wire [31:0] pldStatusPointer,            // Status Pointer for the Payload channel
        //
        output wire        trigPldPassive_p,            // Triggers the Payload Primary Controller FSM to PASSIVE
        output wire        trigPldHalt_p,               // Triggers the Payload Primary Controller FSM to HALTED 
        output wire        trigPldActive_p,             // Triggers the Payload Primary Controller FSM to ACTIVE
        output wire        trigPldDead_p,               // Triggers the Payload Primary Controller FSM to DEAD
        output wire        updPldStaPtr_p,              // Updates the status pointer of the payload primary Controller
        output reg  [31:0] nxtPldDescPtr,               // The address to which the status pointer of the payload channel
                                                        // should be updated to.
        output reg         rxPayUPatternErr,            // Receive Payload Unique Pattern Error
        output reg         rxPayBusErr,                 // Receive Payload Bus Error
        output reg         rxPayNextPointerErr,         // Receive Payload Next Pointer Error
     
        //$port_g macController interface
        input wire         frameRxed_p,                 // Frame is received completely. Received from MAC Controller.
                                                        // Generated after the FCS check is done and FCS is correct
        output wire        rxListProcCsIsIdle,          // Data read from RX FIFO

        //$port_g rxController interface
        output reg         rxFrmDiscard,                // Discard the current rx frame : no more descriptor and rxFlowCntrlEn == 1
        output reg         rxDescAvailable,             // Indicate to rxController that Current frame has a all necessaries descripstor

        input  wire        rxFrmDiscardRet,             // Return signal on rxFrmDiscard from macCLk domain to macPIClk domain
        //$port_g interrupt controller interface
        output wire        rxTrigger,                   // Interrupt indicating a frame has been received
                                                        // Is generated when the interruptEnRx bit in the RHD is set
        output wire        counterRxTrigger,            // Interrupt indicating that the processed number of payload descriptor
                                                        // if bigger or equal to 
        output wire        rxTrig_p,                    // Indicate that the RX Descriptor Done has been written
        
        //$port_g registers interface
        input  wire        rxFlowCntrlEn,               // Enable Rx Flow Control
        input  wire  [7:0] rxPayloadUsedCount,          // Received Payload Used Count
        output reg  [31:0] rxPayCurrentPointer,         // Keeps track of the payload linked list

        output reg  [15:0] rxListProcDebug,
        output wire [15:0] debugPortRxListA,            // Debug purpose

        //$port_g debug port interface
        output reg  [ 4:0] rxListProcCs                 // Current state register
                                                        
                                                        
);


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// rxListProc FSM states definition
//$fsm_sd rxListProc
localparam
   IDLE                = 5'd0   ,     //SW has not queued any descriptors
   WAIT_HDR_CS_PASSIVE = 5'd1   ,     //Wait till HDR DMA channel is PASSIVE
   FETCH_HDR_DESC      = 5'd2   ,     //raise reques to fetch header descriptor
   WAIT_HDR_DESC_DONE  = 5'd3   ,     //wait until header descr fetch is over
   CHK_FRM_STRT        = 5'd4   ,     //Positions RX FIFO ptr to start of hdr
   MOVE_HDR_TO_MEM     = 5'd5   ,      //request to start moving hdr from FIFO
   WAIT_HDR_DONE       = 5'd6   ,      //wait till hdr movement request is over
   WAIT_TH_EOP         = 5'd7   ,      //Wait till frameRxed or end of packet
   WAIT_PLD_CS_PASSIVE = 5'd8   ,      //Wait until Pld DMA channel is PASSIVE
   UPD_CURR_PTR        = 5'd9   ,
   FETCH_PLD_DESC      = 5'd10  ,      //raise request to fetch payload descript
   WAIT_PLD_DESC_DONE  = 5'd11  ,      //wait till payload descr fetch is over
   MOVE_PLD_TO_MEM     = 5'd12  ,      //request to start moving payload to mem
   WAIT_PLD_DONE       = 5'd13  ,      //wait till data movement request is over
   WR_LAST_PLD_PTR     = 5'd14  ,
   WAIT_WR_LAST_PLD_PTR= 5'd15  ,
   WR_PLD_PTR_REF      = 5'd16  ,      //req to write first pld ptr 2 rx hdrdesc
   WAIT_WR_PLD_PTR_REF = 5'd17  ,      //wait till write of 1st pld ptr is done
   WR_FRM_LEN          = 5'd18  ,      //req to Write frm length to rx hdrdescr
   WAIT_WR_FRM_LEN     = 5'd19  ,     //wait till wr frm len is done
   UPD_DESC_FLDS       = 5'd20  ,     //request to update the descriptor fields
   WAIT_UPD_DESC_FLDS  = 5'd21  ,     //wait til descriptor fields are updated
   UPD_STAT            = 5'd22  ,     //trig updation of stat ptr in Prim Ctlr
   TRIG_HDR_PASSIVE    = 5'd23  ,     //Triggers Header prim ctlr to PASSIVE
   TRIG_PLD_PASSIVE    = 5'd24  ,     //Triggers Payload prim ctlr to PASSIVE
   TRIG_HDR_HALTED     = 5'd25  ,     //no more descriptors available for hdr
   TRIG_PLD_HALTED     = 5'd26  ,     //no more descriptors available for pld
   HDR_DMA_ERROR       = 5'd27  ,     //Error encountered during a transfer
   PLD_DMA_ERROR       = 5'd28  ,     //Error encountered during a transfer
   FRM_DISCARD         = 5'd29  ,     //Discard Rx Frame du to descriptor error
   WAIT_FRM_DISCARD    = 5'd30  ;     //Discard Rx Frame du to descriptor error

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
// String definition to display rxListProc current state
reg [20*8:0] rxListProcCs_str;
`endif // RW_SIMU_ON

reg         saveFrmFlag;               //Flag indicates saveFrm_p has occurred
reg         discardFrmFlag;            //Flag indicates discardFrm_p has occurred
reg         endPldFlag;                //Flag indicates endPld_p has occurred
reg         endHdrFlag;                //Flag indicates endHdr has occurred
reg         rxInterrupt;               //Stores the value of the interruptEnRx bit
                                       //in the RHD 
reg         upd2StatPtr;               //Indicates the currPtr should be updated to
                                       //status pointer
reg  [15:0] quadletsRead;              //the total number of quadlets read
reg  [ 4:0] rxListProcNs;              //Next state register
reg  [31:0] hdrBufStartPtr;            //Start ptr for buffer associated with hdr descr
reg  [15:0] hdrBufEndPtr;              //end ptr for buffer associated with hdr descr 
reg  [31:0] pldBufStartPtr;            //start ptr for buffer associated with pld descr
reg  [15:0] pldBufEndPtr;              //end ptr for buffer associated with pld desc

reg         rdFifoValid;               // rx fifo flop 

wire        startHdr_p;                //I ndicates the first quadlet of the received frm
reg         startHdr;                  // Indicates the first quadlet of the received frm
wire        endHdr;                    // indicates the last quadlet of the header for the
                                       // received packet in case of data packets
wire        endPld;                    // indicates the last quadlet of the payload for 
                                       // the received packet
wire        discardFrm_p;              // discard the current frame in the receive fifo 
wire        saveFrm_p;                 // save the current received frame present in the
                                       // receive fifo 
wire        nxtHdrDescValid;           // Next header descriptor pointer is valid
reg         nxtPldDescValid;           // Next payload descriptor pointer is valid
wire        pointerNotAligned;         // pointer is not aligned
reg         payloadDescDone;           // Payload descriptor has been used already
reg         pldPatternError;           // asserted when the pattern is not found in a pld
                                       // descriptor
reg         hdrPatternError;           // asserted when the pattern is not found in a hdr
                                       // descriptor

wire        hdrStatePassive;           // indicates header channel FSM is in PASSIVE
wire        hdrStateActive;            // indicates header channel FSM is in ACTIVE
wire        pldStatePassive;           // indicates payload channel FSM is in PASSIVE
wire        pldStateActive;            // indicates payload channel FSM is in ACTIVE

wire [15:0] pldBufLength;              // Indicates length of buffer in pld desc
wire [15:0] pldBufLengthInQuads;       // Indicates length of pld buffer in Quads
wire [15:0] hdrBufLength;              // Indicates length of buffer in hdr desc
wire [15:0] hdrBufLengthInQuads;       // Indicates length of hdr buffer in quads
reg  [31:0] firstPldDescPtr;           // First payload descripto pointer to read write controller
                                       // block to update in the receive header descriptor

reg         hdrDescriptorDone;         // Indicate the Header descriptor has been processed by HW
reg         lastBuffer;                // Gives the information the buffer is the last for the MPDU

reg         frameRxed;                 // indicates a complete frame is received and is in FIFO

wire        aboveThreshold;            // Indicates there is substantial data present in the RX fifo

// transaction management
reg         transactionEnable_p;       // this signal indicate the start of a transaction on the AHB
reg  [15:0] transactionSize;           // this signal indicate the transaction size
reg         transactionType;           // this signal indicate the type of transaction. 0 for read, 1 for write
wire        transactionDone_p;         // this signal indicate the end of the transaction
reg         stopTransaction;           // this signal indicate the transaction should be stopped
reg         waitingTransEnd;           // Indicates we are waiting the end of the transaction
reg         ongoingTransaction;        // when a transaction requested, this signal is assserted until all the data are transfered
reg         ongoingBurst;              // indicate the a burst is ongoing
reg         burstStart_p;              // indicate a burst should be started
reg         burstStop_p;               // indicate a burst should be stop
reg  [15:0] remainingData;             // this signal indicate the number of byte to transfer remaining

wire [31:0] pldDescStatus;             // status to be written into the pld desc
reg         emptyBeforeEnd;            // indicate there is not anymore buffers while the reception is not finished

reg   [7:0] oldnRxPayloadDescUsed;     // Store the value of nRxPayloadDescUsed when the frame reception started.
reg   [7:0] nRxPayloadDescUsed;        // number of payload descriptors consumed

reg  [3:0] rxListProcDebugCnt;
reg [31:0] rxListProcDebugLen;
reg [31:0] rxListProcDebugStatus;
reg [31:0] rxListProcDebugAddr;

reg [15:0] rxMPDUQuadtletLength;       // Caputred value from fifo (MPDU length + trailler)
reg        rxPldDescAvailable;         // Detect if the current pld desc can hold the remaining of the rxpkt

reg        discardFromHdr;             // Remeber if discard is generated by no header desc
reg        discardFromPld;             // Remeber if discard is generated by no payload desc

reg        rxNDP;                      // Null data packet
reg        rxHdrNewTailFlag;           // Capture the header primary control new tail for discarded fram due to no more hdr desc
reg        rxPldNewTailFlag;           // Capture the payload primary control new tail for discarded fram due to no more hdr desc

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

//Current State logic
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxListProcCs <= IDLE;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxListProcCs <= IDLE;
  else 
    rxListProcCs <= rxListProcNs;
end


assign rxListProcCsIsIdle = (rxListProcCs == IDLE);

//Next state logic
always @*
begin
  case(rxListProcCs)
    IDLE:
      //$fsm_s The FSM waits in this state till the FIFO threshold has reached or
      //a complete frame has been received
      if ((((rxFlowCntrlEn == 1'b1) && (rxFifoEmpty == 1'b0)) ||
           (aboveThreshold == 1'b1) ||
           (frameRxed_p == 1'b1)    ||
           (frameRxed == 1'b1)) &&
          ((rxPayloadState != 4'h8) &&
           (rxHeaderState != 4'h8)))
        //$fsm_t If the FIFO threshold has reached or
        //a complete frame has been received, the FSM stays in WAIT_HDR_CS_PASSIVE
        rxListProcNs = WAIT_HDR_CS_PASSIVE;
      else 
        //$fsm_t If the FIFO threshold is not reached, the FSM stays in IDLE
        rxListProcNs = IDLE;

   WAIT_HDR_CS_PASSIVE:
      //$fsm_s The FSM waits here till the FSM state of the header primary channel
      //is PASSIVE
      if ((hdrStatePassive == 1'b1) ||
          (hdrStateActive == 1'b1))
        //$fsm_t When the header primary channel is either in PASSIVE or ACTIVE state, 
        //the FSM moves to FETCH_HDR_DESC
        rxListProcNs = FETCH_HDR_DESC;
      else if(rxFlowCntrlEn)
        //$fsm_t When the RX flow control indication is received indicating that there is no header descriptor available, 
        //the FSM moves to FRM_DISCARD
        rxListProcNs = FRM_DISCARD;
      else
        //$fsm_t While the header primary channel is neither in PASSIVE nor ACTIVE state, the FSM stays in WAIT_HDR_CS_PASSIVE
        rxListProcNs = WAIT_HDR_CS_PASSIVE;

    FETCH_HDR_DESC:
      //$fsm_s The request to the read write controller for fetching of header
      //descriptor is raised in this state
      // ahbRead is asserted to indicate DMA Read Write Controller to fetch Rx Header Descriptor from System Memory. 
      // startAddress is assigned to the hdrStatusPointer value and the numQuadlets is assigned to the depth of the Header descriptor.
      // hdrBufStartPtr and hdrBufEndPtr values are registered in this state.
      

      //$fsm_t The FSM moves to WAIT_HDR_DESC_DONE after 1 clock cycle
      rxListProcNs = WAIT_HDR_DESC_DONE;

    WAIT_HDR_DESC_DONE:
      //$fsm_s FSM waits in this state until the entire header descriptor is fetched completely.
      if (transactionDone_p == 1'b1)
      begin
        if (hdrDescriptorDone == 1'b1)
        begin
          if (nxtHdrDescValid == 1'b1)
            //$fsm_t If the RHD fetched is completed but the descriptor is already done
            //then the FSM moves to FETCH_HDR_DESC state
            rxListProcNs = FETCH_HDR_DESC;
          else if(rxFlowCntrlEn)
            //$fsm_t If the rxFlow control is enabled and there is not valid descriptor
            //then the FSM moves to FRM_DISCARD state
            rxListProcNs = FRM_DISCARD;
          else
            //$fsm_t If there is an error once the RHD fetch is completed
            //then the FSM moves to HDR_DMA_ERROR state
            rxListProcNs = HDR_DMA_ERROR;
        end
        else
          //$fsm_t If the RHD fectech is correct
          //then the FSM moves to CHK_FRM_STRT state
          rxListProcNs = CHK_FRM_STRT;
      end
      else if ((hdrPatternError   == 1'b1) ||
               (rxListError       == 1'b1) || 
               (pointerNotAligned == 1'b1))
        //$fsm_t If there is an error indicated by the read write controller
        //during the RHD fetch, then the FSM moves to HDR_DMA_ERROR state
        rxListProcNs = HDR_DMA_ERROR;
      else
        //$fsm_t While nothing is received, the FSM stays in WAIT_HDR_DESC_DONE
        rxListProcNs = WAIT_HDR_DESC_DONE;

    CHK_FRM_STRT:
      //$fsm_s In this state, the FSM waits for the start of Head or NDP from the RX FIFO
      if ((rxTagFifoRdData == 4'b1010) && (rxFifoRd == 1'b1) && (rxFifoRdData == 32'hA)) // rxNDP
      begin
        //$fsm_t If the frame received is a NDP, then the FSM moves to WR_PLD_PTR_REF state
        rxListProcNs = WR_PLD_PTR_REF;
      end
      else if (discardFrmFlag == 1'b1)
      begin
        rxListProcNs = IDLE;
      end
      else if (startHdr == 1'b1)
      begin
        `ifdef RW_MPDU_AC
        //$fsm_t If the frame received is the startHdr indication, then the FSM moves to WAIT_TH_EOP state
        //This transition is available only in RW_MPDU_AC is defined
        rxListProcNs = WAIT_TH_EOP;
        `else
        //$fsm_t If the frame received is the startHdr indication, then the FSM moves to MOVE_HDR_TO_MEM state
        //This transition is available only in RW_MPDU_AC is not defined
        rxListProcNs = MOVE_HDR_TO_MEM;
        `endif
      end 
      else
      begin
        //$fsm_t While nothing is received, the FSM stays in WAIT_HDR_DESC_DONE
        rxListProcNs = CHK_FRM_STRT;
      end

  `ifndef RW_MPDU_AC
    MOVE_HDR_TO_MEM:
      //$fsm_s The request to move header from RX FIFO to the SRAM is asserted
      //in this state
      //ahbWrite is asserted. 
      //numQuadlets is assigned to the difference of the hdrBufStartPtr and hdrBufEndPtr. 
      //startAddress is assigned to the hdrBufStartPtr value.
      //
      //This state is available only in RW_MPDU_AC is not defined

      //$fsm_t The FSM moves to WAIT_HDR_DONE after 1 clock cycle
      rxListProcNs = WAIT_HDR_DONE;


    WAIT_HDR_DONE:
      //$fsm_s Waits till header is transferred from FIFO to local SRAM
      //If in between when fetching the header the RX FIFO goes empty then 
      //the FSM stays in this state until the RX FIFO above threshold is reached
      //and the remaining quadlets are fetched
      //
      //This state is available only in RW_MPDU_AC is not defined
      if (rxListError == 1'b1)
        //$fsm_t In case of an error then FSM moves to HDR_DMA_ERROR state
        rxListProcNs = HDR_DMA_ERROR;
      else if (transactionDone_p == 1'b1)
      begin
        if (discardFrmFlag == 1'b1)
          //$fsm_t If discardFrame_p is received then FSM goes to IDLE. 
          rxListProcNs = IDLE;
        else
          //$fsm_t When the transfer of the Header from the RX FIFO to the SRAM is completed, the FSM moves to WAIT_TH_EOP
          rxListProcNs = WAIT_TH_EOP;
      end                                  
      else                                 
        //$fsm_t While the transfer of the Header from the RX FIFO to the SRAM is not completed, the FSM stays in WAIT_HDR_DONE
        rxListProcNs = WAIT_HDR_DONE;
  `endif

    WAIT_TH_EOP:
      //$fsm_s Waits till end of packet or fifo threshold is reached
      if (((rxFlowCntrlEn == 1'b1) && (rxFifoEmpty == 1'b0)) ||
          (aboveThreshold == 1'b1) ||
          (frameRxed == 1'b1)      ||
          (frameRxed_p == 1'b1))
        //$fsm_t if the end of packet or fifo threshold reached indication is received, the FSM goes to WAIT_PLD_CS_PASSIVE 
        rxListProcNs = WAIT_PLD_CS_PASSIVE;
      else 
        //$fsm_t While the end of packet or fifo threshold is not reached, the FSM stays in WAIT_TH_EOP
        rxListProcNs = WAIT_TH_EOP;
 
    WAIT_PLD_CS_PASSIVE:
      //$fsm_s The FSM waits here till the FSM state of the payload primary channel
      //is PASSIVE
      if ((pldStatePassive == 1'b1) ||
          (pldStateActive == 1'b1))
        //$fsm_t When the payload primary channel is either in PASSIVE or ACTIVE state, 
        //the FSM moves to UPD_CURR_PTR
        rxListProcNs = UPD_CURR_PTR;
      else if (rxFlowCntrlEn)
        //$fsm_t When the RX flow control indication is received indicating that there is no payload descriptor available, 
        //the FSM moves to FRM_DISCARD
        rxListProcNs = FRM_DISCARD;
      else 
        //$fsm_t While the payload primary channel is neither in PASSIVE nor ACTIVE state, the FSM stays in WAIT_PLD_CS_PASSIVE
        rxListProcNs = WAIT_PLD_CS_PASSIVE;

    UPD_CURR_PTR:
      //$fsm_s  The currPtr value is updated to the pldStatusPtr if upd2StatPtr is high else it is updated to the nxtPldDescPtr. 

      //$fsm_t The FSM moves to FETCH_PLD_DESC after 1 clock cycle
      rxListProcNs = FETCH_PLD_DESC;

  //fetch Payload descriptor request is assserted
    FETCH_PLD_DESC:
      //$fsm_s The request to fetch the Payload Descriptor pointed by the currPtr location is asserted.

      //$fsm_t The FSM moves to WAIT_PLD_DESC_DONE after 1 clock cycle
      rxListProcNs = WAIT_PLD_DESC_DONE;

  
    WAIT_PLD_DESC_DONE:
    //$fsm_s Waits until payload descriptor is fetched.
      if ((pldPatternError == 1'b1) ||
          (rxListError == 1'b1))
        //$fsm_t if pattern is not found or a error is detected during the fetch, then the FSM moves to PLD_DMA_ERROR
        rxListProcNs = PLD_DMA_ERROR;
      else if (transactionDone_p == 1'b1)
      begin
        if ((payloadDescDone == 1'b1) || (emptyBeforeEnd == 1'b1))
        begin
          if (nxtPldDescValid == 1'b1)
            //$fsm_t If the current descriptor is done and the next descriptor is valid,
            //then the FSM moves to UPD_CURR_PTR
            rxListProcNs = UPD_CURR_PTR;
          else if(rxFlowCntrlEn)
            //$fsm_t If the current descriptor is done and the next descriptor is not valid and the RX Flow control is enabled,
            //then the FSM moves to FRM_DISCARD
            rxListProcNs = FRM_DISCARD;
          else
            //$fsm_t If the current descriptor is done and the next descriptor is not valid but the RX Flow control is not enabled, 
            //then the FSM moves to PLD_DMA_ERROR
            rxListProcNs = PLD_DMA_ERROR;
        end
        else if ((rxMPDUQuadtletLength > pldBufLengthInQuads) && (nxtPldDescValid == 1'b0))
        begin
          if(rxFlowCntrlEn == 1'b1)
           //$fsm_t if the length of the MPDU is bigger than the room available in the current payload buffer,
           //the next descriptor is not valid but the RX Flow control is enabled, then the FSM moves to FRM_DISCARD
            rxListProcNs = FRM_DISCARD;
          else
           //$fsm_t if the length of the MPDU is bigger than the room available in the current payload buffer,
           //the next descriptor is not valid and the RX Flow control is disabled, then the FSM moves to PLD_DMA_ERROR
            rxListProcNs = PLD_DMA_ERROR;
        end
        else
          //$fsm_t If all the checks are ok, the FSM moves to MOVE_PLD_TO_MEM
          rxListProcNs = MOVE_PLD_TO_MEM;
      end
      else
        //$fsm_t While the payload descriptor, the FSM stays in WAIT_PLD_CS_PASSIVE
        rxListProcNs = WAIT_PLD_DESC_DONE;

   FRM_DISCARD:
     //$fsm_s Wait until the return signal is catched
     if (rxFrmDiscardRet)
       //$fsm_t When the return signal rxFrmDiscardRet is received, the FSM moves in WAIT_FRM_DISCARD
       rxListProcNs = WAIT_FRM_DISCARD;
     else
       //$fsm_t While the return signal rxFrmDiscardRet is not received, the FSM stays in FRM_DISCARD
       rxListProcNs = FRM_DISCARD;

   // Pop the fifo until discardFrm_p
   WAIT_FRM_DISCARD:
     //$fsm_s Pop the fifo until discardFrm_p
     if (discardFrm_p == 1'b1)
     begin
       if(discardFromHdr == 1'b1)
       begin
         if ((rxHdrNewTailFlag == 1'b1) || (rxHeaderNewTail == 1'b1))
           //$fsm_t When the discardFrm_p signal is received and the discard was due to Header 
           //but a new descriptor has been linked (either with newTail or newHead), the FSM moves in TRIG_HDR_PASSIVE
           rxListProcNs = TRIG_HDR_PASSIVE;
         else
           //$fsm_t When the discardFrm_p signal is received and the discard was due to Header 
           //but no new descriptor has been linked, the FSM moves in TRIG_HDR_HALTED
           rxListProcNs = TRIG_HDR_HALTED;
       end
       else
       begin
         //$fsm_t When the discardFrm_p signal is received  and the discard was not due to Header, 
         //the FSM moves in TRIG_HDR_PASSIVE
         rxListProcNs = TRIG_HDR_PASSIVE;
       end
     end
     else
       //$fsm_t While the discardFrm_p is not received, the FSM stays in WAIT_FRM_DISCARD
       rxListProcNs = WAIT_FRM_DISCARD;

    MOVE_PLD_TO_MEM:
      //$fsm_s Request to start moving payload from RX fifo to Local SRAM is asserted

      //$fsm_t The FSM moves to WAIT_PLD_DONE after 1 clock cycle
      rxListProcNs = WAIT_PLD_DONE;

    WAIT_PLD_DONE:
      //$fsm_s FSM waits in this state until the entire payload buffer is filled or 
      //until the end of payload indication is received.
      if (rxListError == 1'b1)
        //$fsm_t In case of error during the processing, 
        //the FSM moves to PLD_DMA_ERROR
        rxListProcNs = PLD_DMA_ERROR;
      else if (rxListTransComplete == 1'b1)
      begin
        if (discardFrmFlag == 1'b1)
          //$fsm_t If the rxListTransComplete and the discard flag are received 
          //the FSM moves back to IDLE
          rxListProcNs = IDLE;
        else if (endPldFlag == 1'b1)
          //$fsm_t If the rxListTransComplete and the end of payload flag are received 
          //the FSM moves to WR_PLD_PTR_REF
          rxListProcNs = WR_PLD_PTR_REF;
        else if (transactionDone_p == 1'b1)
        begin
          if (nxtPldDescValid == 1'b1)
            //$fsm_t If the rxListTransComplete and the transactionDone_p flag are received 
            //and the next payload descriptor is not valid
            //the FSM moves to WAIT_TH_EOP
            rxListProcNs = WAIT_TH_EOP;
          else
            //$fsm_t If the rxListTransComplete and the transactionDone_p flag are received 
            //and the next payload descriptor is not valid
            //the FSM moves to TRIG_PLD_HALTED
            rxListProcNs = TRIG_PLD_HALTED;
        end
        else 
          //$fsm_t If the rxListTransComplete is received but neither the discard flag 
          // nor the end Playoad flag nor the transaction done flag has been received,
          //the FSM stays in WAIT_PLD_DONE
          rxListProcNs = WAIT_PLD_DONE;
      end  
      else 
         //$fsm_t While the rxListTransComplete is not received, the FSM stays in WAIT_PLD_DONE
        rxListProcNs = WAIT_PLD_DONE;
 
    WR_LAST_PLD_PTR:
      //$fsm_s Update the 2 LSB bit in the 2nd row of the 
      //PLD desc ptr to indicate this is the last pld
      //ptr for the current packet

      //$fsm_t The FSM moves to WAIT_WR_LAST_PLD_PTR after 1 clock cycle
      rxListProcNs = WAIT_WR_LAST_PLD_PTR;

    WAIT_WR_LAST_PLD_PTR:
      //$fsm_s In this state the FSM waits until the request completed indication is received.
      if (rxListError == 1'b1)
        //$fsm_t In case of error during the processing, 
        //the FSM moves to PLD_DMA_ERROR
        rxListProcNs = PLD_DMA_ERROR;
      else if ((transactionDone_p == 1'b1) &&
               (rxListTransComplete == 1'b1))
         //$fsm_t When the rxListTransComplete is received, the FSM stays in UPD_STAT
        rxListProcNs = UPD_STAT;
      else
         //$fsm_t While the rxListTransComplete is not received, the FSM stays in WAIT_WR_LAST_PLD_PTR
        rxListProcNs = WAIT_WR_LAST_PLD_PTR;

    WR_PLD_PTR_REF:
      //$fsm_s Request to read write controller to 
      //write the first payload pointer reference 
      //in the header descriptor

      //$fsm_t The FSM moves to WAIT_WR_PLD_PTR_REF after 1 clock cycle
      rxListProcNs = WAIT_WR_PLD_PTR_REF;

    WAIT_WR_PLD_PTR_REF:
      //$fsm_s wait until the first payload pointer reference
      //is updated in the header descriptor
      if (rxListError == 1'b1)
        //$fsm_t In case of error during the processing, 
        //$fsm_t In case of error during the first payload pointer reference update, 
        //the FSM moves to HDR_DMA_ERROR
        rxListProcNs = HDR_DMA_ERROR;
      else if ((transactionDone_p == 1'b1) &&
               (rxListTransComplete == 1'b1))
         //$fsm_t When the first payload pointer is updated, the FSM moves to WR_FRM_LEN
        rxListProcNs = WR_FRM_LEN; 
      else
         //$fsm_t While the first payload pointer is not updated, the FSM stays in WAIT_WR_PLD_PTR_REF
        rxListProcNs = WAIT_WR_PLD_PTR_REF;

    WR_FRM_LEN:
      //$fsm_s Request to read write controller to write the frame 
      //length to the receive header descriptor

      //$fsm_t The FSM moves to WAIT_WR_FRM_LEN after 1 clock cycle
      rxListProcNs = WAIT_WR_FRM_LEN;

    WAIT_WR_FRM_LEN:
      //$fsm_s wait until the frame length is written by the read 
      //write controller
      if (rxListError == 1'b1)
        //$fsm_t In case of error during the frame length update, 
        //the FSM moves to HDR_DMA_ERROR
        rxListProcNs = HDR_DMA_ERROR;
      else if (rxListTransComplete == 1'b1)
      begin
         //$fsm_t When the frame length has been updated and the frame shall be discarded, 
         //the FSM moves to IDLE
        if (discardFrmFlag)
          rxListProcNs = IDLE;
        else  
         //$fsm_t When the frame length has been updated and the frame has not been discarded, 
         //the FSM moves to UPD_DESC_FLDS
          rxListProcNs = UPD_DESC_FLDS;
      end
      else
         //$fsm_t While the frame length is not updated, the FSM stays in WAIT_WR_FRM_LEN
        rxListProcNs = WAIT_WR_FRM_LEN; 

    UPD_DESC_FLDS:
      //$fsm_s Request to read write controller to update the 
      //descriptor fields

      //$fsm_t The FSM moves to WAIT_UPD_DESC_FLDS after 1 clock cycle
       rxListProcNs = WAIT_UPD_DESC_FLDS;

    WAIT_UPD_DESC_FLDS:
      //$fsm_s Wait until the update of descriptor fields is 
      //completed
      if (rxListError == 1'b1)
        //$fsm_t In case of error during the descriptor fields update, 
        //the FSM moves to HDR_DMA_ERROR
        rxListProcNs = HDR_DMA_ERROR;
      else if (transactionDone_p == 1'b1)
      begin
         if ((saveFrmFlag == 1'b1) && (remainingData == 16'b0))
         begin
           if (rxNDP == 1'b0)
              //$fsm_t if the descriptor fields have been updated and the frame shall be saved and it is not a NDP, 
              //the FSM moves to WR_LAST_PLD_PTR
             rxListProcNs = WR_LAST_PLD_PTR;
           else
              //$fsm_t if the descriptor fields have been updated and the frame shall be saved and it is a NDP, 
              //the FSM moves to UPD_STAT
             rxListProcNs = UPD_STAT;
         end
         else  
              //$fsm_t if the descriptor fields have been updated and the frame shall not be saved, 
              //the FSM moves back to IDLE
           rxListProcNs = IDLE;
      end
      else
         //$fsm_t While the descriptor fields has not been updated, the FSM stays in WAIT_UPD_DESC_FLDS
        rxListProcNs = WAIT_UPD_DESC_FLDS;

    UPD_STAT:
      //$fsm_s Trigger the receive primary controllers to 
      //update the status pointer to the next MPDU
      //descriptor Pointers.
      if ((nxtHdrDescValid == 1'b1) || (rxHdrNewTailFlag == 1'b1) || (rxHeaderNewTail == 1'b1))
         //$fsm_t If the next Header Pointer was  valid or either newTail or newHead was done, 
         //the FSM moves to TRIG_HDR_PASSIVE
        rxListProcNs = TRIG_HDR_PASSIVE;
      else
         //$fsm_t If the next Header Pointer was not valid and neither newTail nor newHead was done, 
         //the FSM moves to TRIG_HDR_HALTED
        rxListProcNs = TRIG_HDR_HALTED;
 
    TRIG_HDR_PASSIVE:
      //$fsm_s Trigger the Header to PASSIVE. This state
      //is reached if there are more descriptors 
      //readily queued by SW to fetch the next fragment 
      if ((rxNDP == 1'b1) || (discardFromHdr == 1'b1))
         //$fsm_t If the frame received is NDP or the discard was due to the Header, 
         //the FSM moves back to IDLE
        rxListProcNs = IDLE;
      else if ((nxtPldDescValid == 1'b1) || (rxPldNewTailFlag == 1'b1) || (rxPayloadNewTail == 1'b1) || (discardFromPld == 1'b1))
         //$fsm_t If the next Payload Pointer was valid or either newTail or newHead was done, 
         //the FSM moves to TRIG_PLD_PASSIVE
        rxListProcNs = TRIG_PLD_PASSIVE;
      else
         //$fsm_t If the next Payload Pointer was not valid and neither newTail nor newHead was done, 
         //the FSM moves to TRIG_PLD_HALTED
        rxListProcNs = TRIG_PLD_HALTED;

    TRIG_HDR_HALTED:
      //$fsm_s Trigger the Header to Halted. This state 
      //is reached if there are no more descriptors
      //readily available to fetch the next fragment
      if ((rxNDP == 1'b1) || (discardFromHdr == 1'b1))
         //$fsm_t If the frame received is NDP or the discard was due to the Header, 
         //the FSM moves back to IDLE
        rxListProcNs = IDLE;
      else if ((nxtPldDescValid == 1'b1) || (rxPldNewTailFlag == 1'b1) || (rxPayloadNewTail == 1'b1) || (discardFromPld == 1'b1))
         //$fsm_t If the next Payload Pointer was valid or either newTail or newHead was done, 
         //the FSM moves to TRIG_PLD_PASSIVE
        rxListProcNs = TRIG_PLD_PASSIVE;
      else
         //$fsm_t If the next Payload Pointer was not valid and neither newTail nor newHead was done, 
         //the FSM moves to TRIG_PLD_HALTED
        rxListProcNs = TRIG_PLD_HALTED;

    TRIG_PLD_HALTED: 
      //$fsm_s Trigger the Payload DMA controller to HALTED   
      //This is reached if there are no more descriptors
      //available for the next fetch
      if ((endPldFlag == 1'b0) && (discardFrmFlag == 1'b0) && (saveFrmFlag == 1'b0))
         //$fsm_t If the frame was not saved and not discarded, 
         //the FSM moves to WAIT_TH_EOP
        rxListProcNs = WAIT_TH_EOP;
      else
         //$fsm_t If the frame was saved or discarded 
         //the FSM moves back to IDLE
        rxListProcNs = IDLE;
   
    TRIG_PLD_PASSIVE:
      //$fsm_s Trigger the Payload DMA controller to PASSIVE
      //This state is reached if there are descriptors  
      //available for the next fetch

      //$fsm_t The FSM moves back to IDLE after 1 clock cycle
      rxListProcNs = IDLE; 

    HDR_DMA_ERROR:
      //$fsm_s HDR DMA channel is in error due to either 
      //dmaHIFBus transaction error or a pattern error
      
      //$fsm_t Only the SW can recover the FSM from this state using SW reset
      rxListProcNs = HDR_DMA_ERROR;

    PLD_DMA_ERROR:
      //$fsm_s PLD DMA channel is in error due to either 
      //dmaHIFBus transaction error or a pattern error
      
      //$fsm_t Only the SW can recover the FSM from this state using SW reset
      rxListProcNs = PLD_DMA_ERROR;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:
      rxListProcNs = IDLE;
    // pragma coverage block = on 
  endcase
end

///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
// handle the management of the arbiter requests
always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
  begin
    waitingTransEnd  <= 1'b0;
    rxListProcReq    <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)
  begin
    waitingTransEnd  <= 1'b0;
    rxListProcReq    <= 1'b0;
  end
  else
  begin
    if (burstStart_p == 1'b1)
      rxListProcReq <= 1'b1;
    else if (burstStop_p == 1'b1)
      rxListProcReq    <= 1'b0;
    if ((burstStop_p == 1'b1) && (rxListTransComplete == 1'b0))
      waitingTransEnd  <= 1'b1;
    else if (rxListTransComplete == 1'b1)
      waitingTransEnd  <= 1'b0;
  end
end

// generate the end of transaction signal

assign transactionDone_p = ((rxListTransComplete == 1'b1) && (remainingData == 16'b0 || stopTransaction)) ? 1'b1 : 1'b0;

always @*
begin
  if ((discardFrmFlag == 1'b1) ||
      (rxListProcCs   == PLD_DMA_ERROR) ||
      (rxListProcCs   == HDR_DMA_ERROR) )
    stopTransaction  = 1'b1;
  else
  begin    
    case (rxListProcCs)
      WAIT_HDR_DONE:
        stopTransaction  = endHdrFlag;
      WAIT_PLD_DONE:
        stopTransaction  = endPldFlag;
      WAIT_UPD_DESC_FLDS:
        stopTransaction  = saveFrmFlag;
      default:
        stopTransaction  = 1'b0;
    endcase
  end
end


// manages the transaction
always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
  begin
    transactionEnable_p <= 1'b0;
    ongoingTransaction  <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)
  begin
    transactionEnable_p <= 1'b0;
    ongoingTransaction  <= 1'b0;
  end
  else
  begin
    // latch the transaction status
    if (transactionEnable_p == 1'b1)
      ongoingTransaction  <= 1'b1;
    else if (transactionDone_p == 1'b1)
      ongoingTransaction  <= 1'b0;
      
    // generate the start transaction signal
    if (ongoingTransaction == 1'b0)
    begin
      if ((rxListProcCs == FETCH_HDR_DESC)  ||
          (rxListProcCs == FETCH_PLD_DESC)  ||
          (rxListProcCs == MOVE_HDR_TO_MEM) ||
          (rxListProcCs == MOVE_PLD_TO_MEM) ||
          (rxListProcCs == WR_PLD_PTR_REF)  || 
          (rxListProcCs == WR_FRM_LEN)      ||
          (rxListProcCs == UPD_DESC_FLDS)   ||
          (rxListProcCs == WR_LAST_PLD_PTR) )
      transactionEnable_p <= 1'b1;
    end
    else
    begin
      transactionEnable_p <= 1'b0;
    end
  end
end

// handling the transaction size
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
  begin
    transactionSize <= 16'd0;
    transactionType <=  1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)
  begin
    transactionSize <= 16'd0;
    transactionType <=  1'b0;
  
  end
  else
  begin
    if ((pldPatternError == 1'b1) || 
        (hdrPatternError == 1'b1) ||
        (rxListError == 1'b1))
    begin
      transactionSize <= 16'd0;
      transactionType <=  1'b0;
    end
    else
    begin
      case (rxListProcCs)
        FETCH_HDR_DESC:  
        begin
          transactionSize <= `SIZE_RX_HDR_DESC;
          transactionType <=  1'b0;
        end
        FETCH_PLD_DESC:  
        begin
          transactionSize <= `SIZE_RX_PLD_DESC;
          transactionType <=  1'b0;
        end
        MOVE_HDR_TO_MEM: 
        begin
          transactionSize <= hdrBufLengthInQuads[15:0];
          transactionType <=  1'b1;
        end
        MOVE_PLD_TO_MEM: 
        begin
          transactionSize <= pldBufLengthInQuads[15:0];
          transactionType <=  1'b1;
        end
        WR_LAST_PLD_PTR: 
        begin
          transactionSize <= 16'd1; 
          transactionType <=  1'b1;
        end
        WR_FRM_LEN:      
        begin
          transactionSize <= 16'd1;
          transactionType <=  1'b1;
        end
        WR_PLD_PTR_REF:  
        begin
          transactionSize <= 16'd1;
          transactionType <=  1'b1;
        end
        UPD_DESC_FLDS:   
        begin
          transactionSize <= 16'd9;
          transactionType <=  1'b1;
        end
        default:         
        begin
          transactionSize <= transactionSize;
          transactionType <=  transactionType;
        end
      endcase
    end
  end
end

// manage the number of remaining data
always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n) 
begin
  if (macPIRxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    remainingData <= 16'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    remainingData <= 16'b0;
  end
  else
  begin
    if (transactionEnable_p == 1'b1)
      remainingData <= transactionSize ;
    if ((remainingData != 16'b0) &&                                   // decrement when remaining data is not 0 and
        (((rxListRead  == 1'b1) && (rxListReadDataValid == 1'b1)) ||  // we are in read and there is a read data valid or
         ((rxListWrite == 1'b1) && (rxListNextData == 1'b1))))        // we are in write and a write ready is asserted
      remainingData <= remainingData - 16'b1;
      
  end
end


// startburst management
// inidicate a burst is active
always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n) 
begin
  if (macPIRxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    ongoingBurst <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    ongoingBurst <= 1'b0;
  end
  else
  begin
    // if the burst is completed
    if ( rxListTransComplete  == 1'b1)
      ongoingBurst <= 1'b0;
    // if the burst is started
    else if (burstStart_p == 1'b1)
      ongoingBurst <= 1'b1;
  end 
end

// assign  burstStart_p =  (ongoingTransaction == 1'b1 &&           // start burst when we are in a transaction
//                          !rxFifoEmpty  &&                        // and the Rx FIFO is not Emtpy
//                          remainingData != 0 &&                   // and there are remaining data to be sent
//                          ongoingBurst == 1'b0) ? 1'b1 : 1'b0;    // and we are not already in a burst

always @*
begin
  if ((rxListProcCs == WAIT_HDR_DONE)      ||
      (rxListProcCs == WAIT_PLD_DONE)      ||
      (rxListProcCs == WAIT_WR_FRM_LEN)    || 
      (rxListProcCs == WAIT_UPD_DESC_FLDS) )
  begin
    if ((ongoingTransaction == 1'b1) &&           // start burst when we are in a transaction
        !rxFifoEmpty  &&                          // and the Rx FIFO is not Emtpy
        (remainingData != 16'b0) &&                   // and there are remaining data to be sent
        (ongoingBurst == 1'b0))                   // and we are not already in a burst
      burstStart_p = 1'b1;
    else
      burstStart_p = 1'b0;
  end 
  else
  begin
    if ((ongoingTransaction == 1'b1) &&           // start burst when we are in a transaction
        (remainingData != 16'b0) &&                   // and there are remaining data to be sent
        (ongoingBurst == 1'b0))                   // and we are not already in a burst
      burstStart_p = 1'b1;
    else
      burstStart_p = 1'b0;
  end
end
always @*
begin
  if (ongoingTransaction == 1'b1 && waitingTransEnd == 1'b0)
  begin  
    // in case of discard
    if (discardFrmFlag == 1'b1)
    begin
      // check the transaction is a read
      if (transactionType == 1'b0)
      begin
        // check the read is valid
        if (rxListReadDataValid == 1'b1)
          burstStop_p = 1'b1;
        else
          burstStop_p = 1'b0;
      end
      // the transaction is a write
      else
      begin
        // the write is done
        if (rxListNextData == 1'b1)
          burstStop_p = 1'b1;
        else
          burstStop_p = 1'b0;
      end
    end
    else
    begin  
      case (rxListProcCs)
        WAIT_HDR_DESC_DONE:
        begin
          if ((rxListReadDataValid == 1'b1) &&  ((remainingData - 16'b1   == 16'b0) || (rxListLast == 1'b1)))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        WAIT_HDR_DONE:
        begin
          if ((rxListNextData == 1'b1) &&  
              (((remainingData - 16'b1   == 16'b0) || rxFifoEmpty == 1'b1)  ||
               (endHdr == 1'b1) || (endHdrFlag == 1'b1)))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        WAIT_PLD_DESC_DONE:
        begin
          if ((rxListReadDataValid == 1'b1) &&  ((remainingData - 16'b1   == 16'b0)  || (rxListLast == 1'b1)))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        WAIT_PLD_DONE:
        begin
          if ((rxListNextData == 1'b1) &&  
              (((remainingData - 16'b1   == 16'b0) || rxFifoEmpty == 1'b1)  ||
               (endPld == 1'b1) || (endPldFlag == 1'b1)))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        WAIT_WR_LAST_PLD_PTR:
        begin
          if ((rxListNextData == 1'b1) &&  (remainingData - 16'b1   == 16'b0))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        
        end
        WAIT_WR_PLD_PTR_REF:
        begin
          if ((rxListNextData == 1'b1) &&  (remainingData - 16'b1   == 16'b0))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        WAIT_WR_FRM_LEN:
        begin
          if ((rxListNextData == 1'b1) &&  (remainingData - 16'b1   == 16'b0))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        WAIT_UPD_DESC_FLDS:
        begin
          if ((rxListNextData == 1'b1) &&  
              (((remainingData - 16'b1   == 16'b0) || rxFifoEmpty == 1'b1)  ||
               (saveFrmFlag == 1'b1)))
             burstStop_p = 1'b1;
          else
             burstStop_p = 1'b0;
        end
        HDR_DMA_ERROR:
        begin
          burstStop_p = 1'b1;
        end
        PLD_DMA_ERROR:
        begin
          burstStop_p = 1'b1;
        end
        default:
          burstStop_p = 1'b0;
      endcase
    end
  end
  else
  begin
    burstStop_p = 1'b0;
  end
end

always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n) 
begin
  if (macPIRxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxListLast <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    rxListLast <= 1'b0;
  end
  else
  begin
    if(burstStop_p)
    begin
      rxListLast <= 1'b0;
    end
    else if((rxListRead == 1'b1) && (rxListReadDataValid == 1'b1) &&  (remainingData - 16'b1   <= 16'b1))
    begin
      rxListLast <= 1'b1;
    end
  end
end

// handle rx list memory read
always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n) 
begin
  if (macPIRxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxListRead <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    rxListRead <= 1'b0;
  end
  else
  begin
    if (rxListProcGrant == 1'b1)
    begin
      if ((transactionType == 1'b0) && // Assert write when transaction is a read
          (ongoingBurst    == 1'b1) && // burst is active
          (burstStop_p     == 1'b0) && // the burst is not stop
          (waitingTransEnd == 1'b0) )  // the burst is not waiting for the end of transaction
        rxListRead <= 1'b1;
      else 
        rxListRead <= 1'b0;
    end
    else
      rxListRead <= 1'b0;
  end    
end


// handle rx list write
always @ (posedge macPIRxClk or negedge macPIRxClkHardRst_n) 
begin
  if (macPIRxClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rxListWrite <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    rxListWrite <= 1'b0;
  end
  else
  begin
    if (rxListProcGrant == 1'b1)
    begin
      if ((transactionType == 1'b1) &&  // Assert write when transaction is a write
          (ongoingBurst    == 1'b1) &&  // burst is active
          (burstStop_p     == 1'b0) &&  // the burst is not stop
          (waitingTransEnd == 1'b0) )   // the burst is not waiting for the end of transaction
        rxListWrite <= 1'b1;
      else 
        rxListWrite <= 1'b0;
    end
    else
      rxListWrite <= 1'b0;
  end    
end



//Logic for rxListStartAddress
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxListStartAddress <= 32'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxListStartAddress <= 32'b0;
  else 
  begin
    case (rxListProcCs)
      WAIT_HDR_DESC_DONE:
        rxListStartAddress <= hdrStatusPointer; 
      FETCH_PLD_DESC:
      begin
        if (payloadDescDone == 1'b1)
          rxListStartAddress <= nxtPldDescPtr;
        else
          rxListStartAddress <= rxPayCurrentPointer;
      end
      WAIT_HDR_DONE:
      begin
        if (burstStart_p == 1'b1) 
          rxListStartAddress <= hdrBufStartPtr + 4*quadletsRead; 
      end
      WAIT_PLD_DONE:
      begin
        if (burstStart_p == 1'b1) 
          rxListStartAddress <= pldBufStartPtr + 4*quadletsRead;
      end
      //incrementing by 4 because from the base pointer of the payload
      //descriptor this field is one quadlet. And for each quadlet the 
      //address has to be incremented by 4 due to word addressing in dmaHIF
      WR_LAST_PLD_PTR:
        rxListStartAddress <= (rxPayCurrentPointer + 4*4);
      //incrementing by 24 because the from the base pointer
      //this field is 6 quadlets. And for each quadlet the 
      //address has to be incremented by 4 due to word 
      //addressing in the dmaHIF
      WR_FRM_LEN:
        rxListStartAddress <= hdrStatusPointer + {27'd0, 5'd28};
      //incrementing by 8 since the location of this field
      //from the base poitner is 2 quadlets. And for each quadlet
      //the address has to eb incremented by 4 due to word
      //addressing in the dmaHIF
      WR_PLD_PTR_REF:
        rxListStartAddress <= hdrStatusPointer + {28'd0, 4'd8};
      //incrementing by 28 since the location of this field
      //from the base pointer is 7 quadlets. And for each quadlet
      //the address has to be incremented by 4 due to word
      //addressing in the dmaHIF
      WAIT_UPD_DESC_FLDS:
      begin
        if (burstStart_p == 1'b1) 
          rxListStartAddress <= hdrStatusPointer + 32'h20 + 4*quadletsRead;
      end
      default: 
        rxListStartAddress <= rxListStartAddress;
    endcase
  end
end


// manages the access size
assign rxListSize = 3'b010;

// handle the data written to the memory
always@*
begin
  case(rxListProcCs)
    WAIT_HDR_DONE:
      rxListWriteData = rxFifoRdData;
    WAIT_PLD_DONE:
      rxListWriteData = rxFifoRdData;
     WAIT_WR_PLD_PTR_REF:
      rxListWriteData = (rxNDP) ? 32'h0 : firstPldDescPtr;
     WAIT_WR_FRM_LEN:
      rxListWriteData = (rxNDP) ? 32'h0 : rxFifoRdData;
     WAIT_UPD_DESC_FLDS:
      rxListWriteData = rxFifoRdData;
     WAIT_WR_LAST_PLD_PTR:
      rxListWriteData = pldDescStatus;
    default:
      rxListWriteData = 32'b0;  
  endcase
end



// control of the RxFifo read
always @*
begin
  // do not read when the Fifo is empty
  if ( rxFifoEmpty == 1'b1)  
    rxFifoRd = 1'b0;
  // if the frame is discarded stop reading the Fifo, except when reading the FIFO
  else if ( ((discardFrm_p == 1'b1)  || (discardFrmFlag == 1'b1)) && (rxListProcCs != CHK_FRM_STRT))
    rxFifoRd = 1'b0;
  else    
  begin
    case(rxListProcCs)
      // find the begining of the frame
      CHK_FRM_STRT:
        if ( (startHdr_p == 1'b0) && (startHdr == 1'b0) )
          rxFifoRd = 1'b1;
        else
          rxFifoRd = 1'b0;
        
      // process the received header
      WAIT_HDR_DONE:
      begin
        // pop data from fifo if we start a burst of a next data is asserted
        // except for the first transaction, the data has been poped during 
        // the chk_frm_start phase
        if (((endHdr == 1'b0) && (endHdrFlag == 1'b0)) && ((burstStart_p && (remainingData != transactionSize)) || ( rxListNextData && (remainingData > 16'b1))))
          rxFifoRd = 1'b1;
        else
          rxFifoRd = 1'b0;
      end
      // process the received payload
      WAIT_PLD_DONE:
      begin
        `ifdef RW_MPDU_AC
        if (((endPld == 1'b0) && (endPldFlag == 1'b0)) && ((burstStart_p && rxTagFifoRdData != 4'b0001)|| ( rxListNextData && (remainingData > 16'b1))))
          rxFifoRd = 1'b1;
        `else
        if (((endPld == 1'b0) && (endPldFlag == 1'b0)) && (burstStart_p || ( rxListNextData && (remainingData > 16'b1))))
          rxFifoRd = 1'b1;
        `endif
        else
          rxFifoRd = 1'b0;
      end
      WAIT_WR_FRM_LEN:
      begin
        if ((burstStart_p == 1'b1) && (rxNDP == 1'b0))
          rxFifoRd = 1'b1;
        else
          rxFifoRd = 1'b0;
      end
      // update the Header descripto status
      WAIT_UPD_DESC_FLDS:
        if (burstStart_p || ( rxListNextData && (remainingData > 16'b1))) 
          rxFifoRd = 1'b1;
        else
          rxFifoRd = 1'b0;

      // pop rx fifo until discard frame
      WAIT_FRM_DISCARD:
        rxFifoRd = 1'b1;

      default: 
        rxFifoRd = 1'b0;
    endcase
  end
end



//Resample the Rx FIFO read signal to generate a data valid
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
  begin
    rdFifoValid <= 1'b0;
  end
  else if (macPIRxClkSoftRst_n == 1'b0)
  begin
    rdFifoValid <= 1'b0;
  end
  else
  begin
    // sample the rxFifoRd signal comming from the top level
    rdFifoValid <= rxFifoRd;
  end 
end

///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////

// Logic for rx NDP packet
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxNDP <= 1'b0;
  else if((macPIRxClkSoftRst_n == 1'b0) || ((rxListProcCs != IDLE) &&  (rxListProcNs == IDLE)))
    rxNDP <= 1'b0;
  else if ((rxListProcCs == CHK_FRM_STRT) && (rxTagFifoRdData == 4'b1010) && (rxFifoRd == 1'b1) && (rxFifoRdData == 32'hA))
    rxNDP <= 1'b1;
end


// indicate the start header tag is available in the Fifo interface
// Valid only during check frame start
assign startHdr_p = ((rxTagFifoRdData == 4'b0001) && (rdFifoValid == 1'b1) && (rxListProcCs == CHK_FRM_STRT)) ? 1'b1 : 1'b0;

//This signal indicates the current quadlet read from the RX FIFO
//is the start of header of the received frame
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    startHdr   <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    startHdr   <= 1'b0;
  else
  begin
    if (rdFifoValid == 1'b1)
    begin
      if (startHdr_p == 1'b1)
        startHdr <= 1'b1;
      else
        startHdr <= 1'b0;
    end
    else if (burstStart_p == 1'b1)
      startHdr <= 1'b0;
    else if (rxListProcCs == HDR_DMA_ERROR)
      startHdr <= 1'b0;
    else
     startHdr <= startHdr;
  end
end


//Logic for quadletsRead. This keeps a count of 
//the total frame that has been read after every successful
//transfer Done signal.It is kind of redundant on what the 
//quadletsRead signal does although it does not track in the same
//way.It is incremented to the burstSize when the done signal occurs
//and reset whenever a new count is loaded.
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    quadletsRead <= 16'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    quadletsRead <= 16'b0;
  else if ((rxListProcCs == IDLE)             ||
           (transactionDone_p == 1'b1))
    quadletsRead <= 16'b0;
  else if (discardFrm_p)
    quadletsRead <= 16'b0;
  else if ((rxListProcCs == WAIT_HDR_DONE) && endHdr)
    quadletsRead <= 16'b0;
  else if (((rxListProcCs == WAIT_HDR_DESC_DONE) ||
            (rxListProcCs == WAIT_HDR_DONE)      ||
            (rxListProcCs == WAIT_PLD_DESC_DONE) ||
            (rxListProcCs == WAIT_PLD_DONE)      ||
            (rxListProcCs == WAIT_UPD_DESC_FLDS)) &&
            (((rxListReadDataValid == 1'b1) && (rxListRead== 1'b1))|| ((rxListWrite == 1'b1) && (rxListNextData == 1'b1))))
    quadletsRead <= quadletsRead + 16'd1;
end

//Since a packet can have multiple payload descriptors
//the current Pointer points to the latest payload 
//descriptor being handled. 
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPayCurrentPointer <= 32'd0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPayCurrentPointer <= 32'd0;
  else if (((rxListProcCs == MOVE_PLD_TO_MEM)    &&  (payloadDescDone == 1'b1)) ||
           ((rxListProcCs == WAIT_PLD_DESC_DONE) &&  (emptyBeforeEnd  == 1'b1) && (transactionDone_p == 1'b1)))
    rxPayCurrentPointer <= nxtPldDescPtr;
  else if (rxListProcCs == UPD_CURR_PTR)
  begin
    if (emptyBeforeEnd == 1'b0)
    begin
      if (upd2StatPtr == 1'b1)
        rxPayCurrentPointer <= pldStatusPointer; 
      else
        rxPayCurrentPointer <= nxtPldDescPtr;
    end
  end
end

//Indication to Update to Status pointer. This signal is 
//generated for the first payload descriptor of a received
//packet
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    upd2StatPtr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    upd2StatPtr <= 1'b0;
  else if (rxListProcCs == FETCH_HDR_DESC)
    upd2StatPtr <= 1'b1; 
  else if ((rxListProcCs == UPD_CURR_PTR)  ||
           (rxListProcCs == UPD_DESC_FLDS) ||
           (rxListProcCs == IDLE) 
          )
    upd2StatPtr <= 1'b0;
end
  

//Logic for lastBuffer
// indicate the buffer written is the last for the mpdu
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    lastBuffer <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    lastBuffer <= 1'b0;
  else if (rxListProcCs == WR_LAST_PLD_PTR)
    lastBuffer <= 1'b1;
  else if (rxListProcCs == IDLE)
    lastBuffer <= 1'b0;
end

//Logic for frameRxed
//Latches the frameRxed_p. Used in FSM for checking if the
//frame has been received. Between every received frame the 
//FSM will move to IDLE state hence resetting this signal in
//the IDLE state to latch the next frame's received pulse 
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    frameRxed <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    frameRxed <= 1'b0;
  else if ((rxListProcCs == UPD_STAT) || discardFrmFlag || discardFrm_p)
    frameRxed <= 1'b0;
  else if (frameRxed_p == 1'b1)
    frameRxed <= 1'b1;
end





//logic to check when an header descriptor 
//has been already processed by the HW
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    hdrDescriptorDone <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    hdrDescriptorDone <= 1'b0;
  else if (rxListProcCs == WAIT_HDR_DESC_DONE &&
           quadletsRead == `RX_HDR_STATUS_INFO-1)
    hdrDescriptorDone <= rxListReadData[14];
  else if (rxListProcCs == FETCH_HDR_DESC)
    hdrDescriptorDone <= 1'b0;
end

//Logic for hdrBufStartPtr
//The start pointer for the header buffer is stored in this
//variable. At the time when the header descriptor is fetched
//the read write controller parses the header descriptor to 
//give this information to this module
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    hdrBufStartPtr <= 32'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    hdrBufStartPtr <= 32'b0;
  else if ((rxListProcCs == WAIT_HDR_DESC_DONE) &&
           (quadletsRead == `RX_HDR_BUF_START_PTR-1) &&
           (rxListReadDataValid == 1'b1))
    hdrBufStartPtr <= rxListReadData;
end

//Logic for hdrBufEndPtr
//The end pointer for the header buffer is stored in this
//variable. At the time when the header descriptor is fetched
//the read write controller parses the header descriptor to 
//give this information to this module
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    hdrBufEndPtr <= 16'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
   hdrBufEndPtr <= 16'b0;
  else if ((rxListProcCs == WAIT_HDR_DESC_DONE) &&
           (quadletsRead == `RX_HDR_BUF_END_PTR-1) &&
           (rxListReadDataValid == 1'b1))
    hdrBufEndPtr <= rxListReadData;
end

//Logic for rxInterrupt
//This stores the interruptEnRx bit from the RX header descr
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxInterrupt <= 1'b0;
  else if ((macPIRxClkSoftRst_n == 1'b0) || (rxListProcCs == IDLE))
    rxInterrupt <= 1'b0;
  else if ((rxListProcCs == WAIT_HDR_DESC_DONE) &&
           (quadletsRead == `RX_HDR_CTRL_INFO-1) &&
           (rxListReadDataValid == 1'b1))
    rxInterrupt <= rxListReadData[0];
end

//Logic for pldBufStartPtr
//The start pointer for the payload buffer is stored in this
//variable. At the time when the payload descriptor is fetched
//the read write controller parses the payload descriptor to 
//give this information to this module
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    pldBufStartPtr <= 32'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    pldBufStartPtr <= 32'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_PLD_BUF_START_PTR- 16'd1) &&
           (rxListReadDataValid == 1'b1))
    pldBufStartPtr <= rxListReadData;
end

//Logic for pldBufEndPtr
//The end pointer for the payload buffer is stored in this
//variable. At the time when the payload descriptor is fetched
//the read write controller parses the payload descriptor to 
//give this information to this module
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    pldBufEndPtr <= 16'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    pldBufEndPtr <= 16'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_PLD_BUF_END_PTR - 16'd1) &&
           (rxListReadDataValid == 1'b1))
    pldBufEndPtr <= rxListReadData;
end

//Logic for nxtPldDescPtr;
//The next Pyload descriptor pointer is updated when
//the payload descriptor is finished fetching and it 
//is given by the read write controller.
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    nxtPldDescPtr <= 32'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    nxtPldDescPtr <= 32'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_NXT_PLD_DESC_PTR - 16'd1) &&
           (rxListReadDataValid == 1'b1) &&
           (pldPatternError == 1'b0))
    nxtPldDescPtr <= rxListReadData;
  else if ((rxListProcCs == WAIT_FRM_DISCARD) && (discardFromPld == 1'b1))
    nxtPldDescPtr <= firstPldDescPtr;
  else if ( (nxtPldDescValid == 1'b0) &&
            (rxListProcCs == UPD_DESC_FLDS))
    nxtPldDescPtr <= rxPayCurrentPointer;
end

// logic for the next ptr descriptor valid
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    payloadDescDone <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    payloadDescDone <= 1'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_PLD_STATUS_INFO - 16'd1)  &&
           (rxListReadDataValid == 1'b1))
    payloadDescDone <= rxListReadData[1];
end

// logic for the next ptr descriptor valid
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    nxtPldDescValid <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    nxtPldDescValid <= 1'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_NXT_PLD_DESC_PTR ) &&
           (rxListReadDataValid == 1'b1))
  begin  
    if ((nxtPldDescPtr[1:0] == 2'b00) && (nxtPldDescPtr != 16'd0))
      nxtPldDescValid <= 1'b1;
    else
      nxtPldDescValid <= 1'b0;
      
  end
end

//Logic for nxtHdrDescPtr;
//The next header descriptor pointer is updated when
//the header descriptor is finished fetching and it 
//is given by the read write controller.
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    nxtHdrDescPtr <= 32'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    nxtHdrDescPtr <= 32'b0;
  else if ((rxListProcCs == WAIT_HDR_DESC_DONE) &&
           (quadletsRead == `RX_NXT_HDR_DESC_PTR - 16'd1) &&
           (rxListReadDataValid == 1'b1) &&
           (hdrPatternError == 1'b0))
    nxtHdrDescPtr <= rxListReadData;
end

//Patten error is generated when the first quadlet of the header
//descriptor is not the specified PATTERN
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    hdrPatternError <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    hdrPatternError <= 1'b0;
  else if ((rxListProcCs == WAIT_HDR_DESC_DONE) &&
           (quadletsRead == `RX_DMA_PATTERN - 16'd1) &&
           (rxListReadDataValid == 1'b1))
    hdrPatternError <= (rxListReadData != 32'hBAADF00D);
  else if (hdrPatternError && (rxListProcCs != WAIT_HDR_DESC_DONE))
    hdrPatternError <= 1'b0;
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    pldPatternError <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    pldPatternError <= 1'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_DMA_PATTERN - 16'd1) &&
           (rxListReadDataValid == 1'b1))
    pldPatternError <= (rxListReadData != 32'hC0DEDBAD);
  else if (pldPatternError && (rxListProcCs != WAIT_PLD_DESC_DONE))
    pldPatternError <= 1'b0;
end

//Logic for firstPldDescPtr
//This register holds the value of the first payload status pointer 
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin 
  if (macPIRxClkHardRst_n == 1'b0)
    firstPldDescPtr <= 32'd0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    firstPldDescPtr <= 32'd0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
           (quadletsRead == `RX_NXT_PLD_DESC_PTR - 16'd1) &&
           (rxListReadDataValid == 1'b1) && 
           (pldPatternError == 1'b0))
    firstPldDescPtr <= pldStatusPointer;
end

//Flag is set to direct the state machine to the 
//next appropriate state when the rxListTransComplete occurs
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    endHdrFlag <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    endHdrFlag <= 1'b0;
  else if (((rxTagFifoRdData != 4'b0010) &&
            (rxListProcCs != WAIT_HDR_DONE)) || 
            (rxListError == 1'b1))
    endHdrFlag <= 1'b0;
  else if (endHdr == 1'b1)
    endHdrFlag <= 1'b1;
end

//Flag is set to direct the state machine to the 
//next appropriate state when the rxListTransComplete occurs
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    endPldFlag <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    endPldFlag <= 1'b0;
 else if (((rxTagFifoRdData != 4'b0101)  &&
            (rxListProcCs != WAIT_PLD_DONE)) ||  
            (rxListError == 1'b1))
    endPldFlag <= 1'b0;
  else if (endPld == 1'b1)
    endPldFlag <= 1'b1;
end

//Flag is set to direct the state machine to the 
//next appropriate state when the rxListTransComplete occurs
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    saveFrmFlag <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    saveFrmFlag <= 1'b0;
  else if (((rxTagFifoRdData != 4'b0000)  &&
            (rxListProcCs != WAIT_UPD_DESC_FLDS)) ||
            (rxListError) == 1'b1)
    saveFrmFlag <= 1'b0; 
  else if (saveFrm_p == 1'b1)
    saveFrmFlag <= 1'b1;
end

//Flag is set to direct the state machine to the 
//next appropriate state when the rxListTransComplete occurs
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    discardFrmFlag <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    discardFrmFlag <= 1'b0;
  else if (((rxTagFifoRdData != 4'b1111) && (rxListProcCs != WAIT_FRM_DISCARD)) ||
           ((rxTagFifoRdData != 4'b0000) && (rxListProcCs == WAIT_FRM_DISCARD)) ||
           (rxListProcCs == IDLE)                                               ||
           (rxListError  == 1'b1)                                                  )
    discardFrmFlag <= 1'b0;
  else if (discardFrm_p == 1'b1)
    discardFrmFlag <= 1'b1;
end

//Capture current MPDU Length 
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxMPDUQuadtletLength <= 16'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxMPDUQuadtletLength <= 16'b0;
  else if ((rxListProcNs == IDLE) && (rxListProcCs != IDLE))
    rxMPDUQuadtletLength <= 16'b0;
  else if (rxTagFifoRdData == 4'b1010)
    rxMPDUQuadtletLength <= rxFifoRdData[15:0];
  else if (rxFifoRd && (rxMPDUQuadtletLength != 15'd0))
    rxMPDUQuadtletLength <= rxMPDUQuadtletLength - 15'd1;
end

assign aboveThreshold = !(rxFifoEmpty || rxFifoAlmEmpty);

//Generated when then entire frame reception is over.
assign pldDescStatus  =  {30'b0, 1'b1, lastBuffer};


//Generated when then entire frame reception is over.
assign trigHdrPassive_p = (rxListProcCs == TRIG_HDR_PASSIVE | discardFrmFlag)
                           ? 1'b1: 1'b0;

//Generated when the entire frame reception is over. 
assign trigPldPassive_p = (rxListProcCs == TRIG_PLD_PASSIVE | discardFrmFlag)
                           ? 1'b1: 1'b0;

//Generated when there are no more Payload descriptors
//queued
assign trigHdrHalt_p = ((rxListProcCs == TRIG_HDR_HALTED) && (rxHeaderNewTail == 1'b0))
                        ? 1'b1 : 1'b0;

//Generated when there are no more Payload descriptors
//queued
assign trigPldHalt_p = ((rxListProcCs == TRIG_PLD_HALTED) && (rxPayloadNewTail == 1'b0))
                        ? 1'b1 : 1'b0;

//Triggers the header primary Channel FSM to ACTIVE when there
//is a packet reception and the FIFO threshold is crossed
assign trigHdrActive_p = ((rxListProcCs == WAIT_HDR_CS_PASSIVE) &&
                          (hdrStatePassive == 1'b1))
                          ? 1'b1 : 1'b0;

//Triggers the payload primary Channel FSM to ACTIVE when there
//is a packet reception and hte FIFO threshold is crossed
assign trigPldActive_p = ((rxListProcCs == WAIT_PLD_CS_PASSIVE) &&
                          (pldStatePassive == 1'b1))
                          ? 1'b1 : 1'b0;

//Triggers the Payload to DEAD state when there is an error
//in the bus transaction or when the pattern is not found
assign trigPldDead_p = (rxListProcCs == PLD_DMA_ERROR) 
                        ? 1'b1 : 1'b0;

//Triggers the Header to DEAD state when there is an error
//in the bus transaction or when the pattern is not found
assign trigHdrDead_p = (rxListProcCs == HDR_DMA_ERROR)
                        ? 1'b1 : 1'b0;

//Indication to set the bit for the 1st bit of the
//DMA Status 3 register
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxHdrUPatternErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxHdrUPatternErr <= 1'b0;
  else if (hdrPatternError == 1'b1)
    rxHdrUPatternErr <= 1'b1;
end

//Indication to set the bit for the 2nd bit of the
//DMA Status 3 register
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPayUPatternErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPayUPatternErr <= 1'b0;
  else if (pldPatternError == 1'b1)
    rxPayUPatternErr <= 1'b1;
end

// 3rd
//Indication when a bus error is detection during PLD processing
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxHdrNextPointerErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxHdrNextPointerErr <= 1'b0;
  else if (rxListProcCs == HDR_DMA_ERROR)
    rxHdrNextPointerErr <= nxtHdrDescValid;
end

// 4th
//Indication when a bus error is detection during PLD processing
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPayNextPointerErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPayNextPointerErr <= 1'b0;
  else if (rxListProcCs == PLD_DMA_ERROR)
    rxPayNextPointerErr <= nxtPldDescValid;
end


//Indication when a bus error is detection during HDR processing
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxHdrBusErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxHdrBusErr <= 1'b0;
  else if ((rxListError == 1'b1) &&
          ((rxListProcCs == WAIT_HDR_DESC_DONE) ||
           (rxListProcCs == WAIT_HDR_DONE)))
    rxHdrBusErr <= 1'b1;
end

//Indication when a bus error is detection during PLD processing
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPayBusErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPayBusErr <= 1'b0;
  else if ((rxListError == 1'b1) &&
          ((rxListProcCs == WAIT_PLD_DESC_DONE) ||
           (rxListProcCs == WAIT_PLD_DONE)))
    rxPayBusErr <= 1'b1;
end


//Indicate no more buffers are available while the packet has not been completely received
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    emptyBeforeEnd <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    emptyBeforeEnd <= 1'b0;
  else if ((rxListProcCs == TRIG_PLD_HALTED) && (endPldFlag == 1'b0) && (discardFrmFlag == 1'b0) && (saveFrmFlag == 1'b0)) 
    emptyBeforeEnd <= 1'b1;
  else if ((rxListProcCs == IDLE) || ((rxListProcCs == WAIT_PLD_DESC_DONE) && (transactionDone_p == 1'b1)))
    emptyBeforeEnd <= 1'b0;
end

//Indicate no more buffers are available while the packet has not been completely received
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxFrmDiscard <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxFrmDiscard <= 1'b0;
  else if ((rxListProcCs != IDLE) && (rxListProcNs == IDLE))
    rxFrmDiscard <= 1'b0;
  else if ((rxListProcCs != FRM_DISCARD) && (rxListProcNs == FRM_DISCARD))
    rxFrmDiscard <= 1'b1;
end

// Indicate to rxController that the DMA has all the needed desc for the current rx frame.
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxDescAvailable <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxDescAvailable <= 1'b0;
  else if (rxFlowCntrlEn == 1'b0)
    rxDescAvailable <= 1'b1;
  else if ((rxListProcCs != IDLE) && (rxListProcNs == IDLE))
    rxDescAvailable <= 1'b0;
  else if ((!nxtHdrDescValid && hdrDescriptorDone) || (!nxtPldDescValid && payloadDescDone) || !rxPldDescAvailable)
    rxDescAvailable <= 1'b0;
  else if (!hdrDescriptorDone && !payloadDescDone && rxPldDescAvailable)
    rxDescAvailable <= 1'b1;
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPldDescAvailable <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPldDescAvailable <= 1'b0;
  else if ((rxListProcCs != IDLE) && (rxListProcNs == IDLE))
    rxPldDescAvailable <= 1'b0;
  else if ((rxListProcCs == WAIT_PLD_DESC_DONE) && (rxListProcNs != WAIT_PLD_DESC_DONE) && (rxFlowCntrlEn == 1'b1))
  begin
    if ((rxMPDUQuadtletLength <= pldBufLengthInQuads) || (nxtPldDescValid == 1'b1))
      rxPldDescAvailable <= 1'b1;
    else
      rxPldDescAvailable <= 1'b0;
  end
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    discardFromHdr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    discardFromHdr <= 1'b0;
  else if ((rxListProcCs != IDLE) && (rxListProcNs == IDLE))
    discardFromHdr <= 1'b0;
  else if (((rxListProcCs == WAIT_HDR_CS_PASSIVE) || (rxListProcCs == WAIT_HDR_DESC_DONE)) && (rxListProcNs == FRM_DISCARD) && (rxFlowCntrlEn == 1'b1))
    discardFromHdr <= 1'b1;
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    discardFromPld <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    discardFromPld <= 1'b0;
  else if ((rxListProcCs != IDLE) && (rxListProcNs == IDLE))
    discardFromPld <= 1'b0;
  else if (((rxListProcCs == WAIT_PLD_CS_PASSIVE) || (rxListProcCs == WAIT_PLD_DESC_DONE)) && (rxListProcNs == FRM_DISCARD) && (rxFlowCntrlEn == 1'b1))
    discardFromPld <= 1'b1;
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxHdrNewTailFlag <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxHdrNewTailFlag <= 1'b0;
  else if ((discardFrm_p == 1'b1) || ((rxListProcCs != IDLE) && (rxListProcNs == IDLE)))
    rxHdrNewTailFlag <= 1'b0;
  else if ((rxHeaderNewTail == 1'b1) && (rxHdrNewTailFlag == 1'b0) && (rxListProcCs != IDLE))
    rxHdrNewTailFlag <= 1'b1;
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPldNewTailFlag <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPldNewTailFlag <= 1'b0;
  else if ((discardFrm_p == 1'b1) || ((rxListProcCs != IDLE) && (rxListProcNs == IDLE)))
    rxPldNewTailFlag <= 1'b0;
  else if ((rxPayloadNewTail == 1'b1) && (rxPldNewTailFlag == 1'b0) && (rxListProcCs != IDLE))
    rxPldNewTailFlag <= 1'b1;
end

//Flag indicates if the DMA header state is PASSIVE
assign hdrStatePassive = rxHeaderState[1];

//Flag indicates if the DMA header state is ACTIVE
assign hdrStateActive = rxHeaderState[2];

//Flag indicates if the DMA payload state is PASSIVE
assign pldStatePassive = rxPayloadState[1]; 

assign pldStateActive = rxPayloadState[2];

//triggers the updation of the header status pointer to the next
//pointer after moving the received frame from the FIFO to the 
//local SRAM
assign updHdrStaPtr_p = ((rxListProcCs == UPD_STAT) ||
                         ((rxListProcCs == WAIT_HDR_DESC_DONE) && hdrDescriptorDone)) 
                         ? 1'b1 : 1'b0;

//triggers the updation of the payload status pointer to the next
//pointer after moving the received frame from the FIFO to the 
//local SRAM
assign updPldStaPtr_p = (((rxListProcCs == UPD_STAT) && !rxNDP) ||
                        ((rxListProcCs == FETCH_PLD_DESC) &&  (payloadDescDone == 1'b1)))
                         ? 1'b1 : 1'b0;

//signal indicating the length of the payload buffer
assign pldBufLength = pldBufEndPtr - pldBufStartPtr[15:0];

//Payload Buffer length in quadlets
assign pldBufLengthInQuads = (pldBufLength[1:0] == 2'b0) ? {2'b00,pldBufLength[15:2]} : 
                                                  ({2'b00,pldBufLength[15:2]} + 16'd1);

//Signal indication the length of the header buffer
assign hdrBufLength = hdrBufEndPtr - hdrBufStartPtr[15:0];

//header buffer length in quadlets. shifting by 2 bits
//to divide the length in bytes by 4
assign hdrBufLengthInQuads = (hdrBufLength[1:0] == 2'b0) ? {2'b00,hdrBufLength[15:2]} : 
                                                               ({2'b00,hdrBufLength[15:2]} + 16'd1);

//Patten error is generated when the first quadlet of the header
//descriptor is not the specified PATTERN
//assign hdrPatternError = ((rxListProcCs == WAIT_HDR_DESC_DONE) &&
//                          (rxListReadData != 32'hBAADF00D) &&
//                          (quadletsRead == `RX_DMA_PATTERN - 16'd1) &&
//                          (rxListReadDataValid == 1'b1))
//                          ? 1'b1 : 1'b0;
//
//assign pldPatternError = ((rxListProcCs == WAIT_PLD_DESC_DONE) &&
//                          (rxListReadData != 32'hC0DEDBAD) &&
//                          (quadletsRead == `RX_DMA_PATTERN - 16'd1) &&
//                          (rxListReadDataValid == 1'b1))
//                          ? 1'b1 : 1'b0;

assign nxtHdrDescValid = ((nxtHdrDescPtr[1:0] == 2'b00) && (nxtHdrDescPtr != 0)) ? 1'b1 : 1'b0;

// indicate a pointer error
assign pointerNotAligned = ((nxtPldDescPtr[1:0] != 2'b00) ||
                            (nxtHdrDescPtr[1:0] != 2'b00)) ? 1'b1 : 1'b0 ;



//TAG Decoder logic
//This signal indicates the previous frame in the FIFO needs to 
// be saved
assign saveFrm_p = ((rxTagFifoRdData == 4'b0000)  &&
                    (rdFifoValid == 1'b1)  && (rxListProcCs != CHK_FRM_STRT) && (rxListProcCs != WAIT_FRM_DISCARD))
                    ? 1'b1: 1'b0;

//This signal indicates the previous frame in the FIFO needs to
//be discarded
assign discardFrm_p = ( ((rxTagFifoRdData == 4'b1111) || ((rxTagFifoRdData == 4'b0000) && (rxListProcCs == WAIT_FRM_DISCARD))) &&
                        (rdFifoValid == 1'b1) )
                       ? 1'b1: 1'b0;

//This signal indicates the current quadlet is the end of the header
//of the received frame
assign endHdr = ((rxTagFifoRdData == 4'b0010) && (rdFifoValid == 1'b1) &&
                  (endHdrFlag == 1'b0))
                  ? 1'b1: 1'b0;

//This signal indicates the current quadlet is the end of the Payload
//of the received frame
assign endPld = ((rxTagFifoRdData == 4'b0101) && (rdFifoValid == 1'b1) &&
                 (endPldFlag == 1'b0))
                 ? 1'b1 : 1'b0;


////////////////////////////////////////////////////////////////////////////////
// RX Interrupt Generation
////////////////////////////////////////////////////////////////////////////////

//Trigger indicating frame has been received and transferred to SRAM
//if the receive header descriptor had the rxInterruptEn bit set
assign rxTrigger = (((rxInterrupt == 1'b1)) &&
                    ((rxListProcCs == UPD_STAT))) ? 1'b1 : 1'b0;




// Generation of counterRxTrigger interrupt
assign counterRxTrigger = (rxPayloadUsedCount <= nRxPayloadDescUsed) && ((rxListProcCs == UPD_CURR_PTR) || (rxListProcCs == UPD_STAT));

// Counter nRxPayloadDescUsed whioch counts the number of rx Payload descriptor used.
// It is reset by the hard/soft reset and when the counterRxTrigger is generated
// It is incremented each time a new payload descriptor is fetched
// If the frame is discarded, it is reload with its initial value 
// (before starting the reception of the current frame)
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    nRxPayloadDescUsed <= 8'b0;
  else if ((macPIRxClkSoftRst_n == 1'b0) || counterRxTrigger)
    nRxPayloadDescUsed <= 8'b0;
  else if (discardFrm_p)
    nRxPayloadDescUsed <= oldnRxPayloadDescUsed;
  else if (rxListProcCs == FETCH_PLD_DESC)
    nRxPayloadDescUsed <= nRxPayloadDescUsed + 8'd1;
end

// Store the value of nRxPayloadDescUsed when the frame reception started.
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    oldnRxPayloadDescUsed <= 8'b0;
  else if ((macPIRxClkSoftRst_n == 1'b0) || counterRxTrigger)
    oldnRxPayloadDescUsed <= 8'b0;
  else if (rxListProcCs == WR_LAST_PLD_PTR)
    oldnRxPayloadDescUsed <= nRxPayloadDescUsed;
end

// Indicate that the RX Descriptor Done has been written
assign  rxTrig_p   = (rxListProcCs == UPD_STAT)  ? 1'b1 : 1'b0;


////////////////////////////////////////////////////////////////////////////////
// Debug Interface
////////////////////////////////////////////////////////////////////////////////
                                   

assign debugPortRxListA     = {rxListProcCs[4:0],
                               remainingData[4:0],
                               transactionDone_p,
                               stopTransaction,
                               burstStart_p,
                               burstStop_p,
                               rxListLast,
                               rxListProcReq
                              };

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
  begin
    rxListProcDebug    <= 16'b0;
    rxListProcDebugCnt <= 4'd0;
  end
  else if (saveFrm_p)
  begin
    rxListProcDebug    <= rxListStartAddress[31:16];
    rxListProcDebugCnt <= 4'd1;
  end
  else if (rxListProcDebugCnt == 4'd1) 
  begin
    rxListProcDebug    <= rxListProcDebugAddr[15:0];
    rxListProcDebugCnt <= 4'd2;
  end
  else if (rxListProcDebugCnt == 4'd2) 
  begin
    rxListProcDebug    <= firstPldDescPtr[31:16];
    rxListProcDebugCnt <= 4'd3;
  end
  else if (rxListProcDebugCnt == 4'd3) 
  begin
    rxListProcDebug    <= firstPldDescPtr[15:0];
    rxListProcDebugCnt <= 4'd4;
  end
  else if (rxListProcDebugCnt == 4'd4) 
  begin
    rxListProcDebug    <= rxListProcDebugLen[31:16];
    rxListProcDebugCnt <= 4'd5;
  end
  else if (rxListProcDebugCnt == 4'd5) 
  begin
    rxListProcDebug    <= rxListProcDebugLen[15:0];
    rxListProcDebugCnt <= 4'd6;
  end
  else if (rxListProcDebugCnt == 4'd6) 
  begin
    rxListProcDebug    <= rxListProcDebugStatus[31:16];
    rxListProcDebugCnt <= 4'd7;
  end
  else if (rxListProcDebugCnt == 4'd7) 
  begin
    rxListProcDebug    <= rxListProcDebugStatus[15:0];
    rxListProcDebugCnt <= 4'd8;
  end
  else if (rxListProcDebugCnt == 4'd8) 
  begin
    rxListProcDebug    <= nxtPldDescPtr[31:16];
    rxListProcDebugCnt <= 4'd9;
  end
  else if (rxListProcDebugCnt == 4'd9) 
  begin
    rxListProcDebug    <= nxtPldDescPtr[15:0];
    rxListProcDebugCnt <= 4'd10;
  end
  else if (rxListProcDebugCnt == 4'd10) 
  begin
    rxListProcDebug    <= rxPayCurrentPointer[31:16];
    rxListProcDebugCnt <= 4'd11;
  end
  else if (rxListProcDebugCnt == 4'd11) 
  begin
    rxListProcDebug    <= rxPayCurrentPointer[15:0];
    rxListProcDebugCnt <= 4'd12;
  end
  else if (rxListProcDebugCnt == 4'd12) 
  begin
    rxListProcDebug    <= 16'hffff;
    rxListProcDebugCnt <= 4'd0;
  end
end

always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
  begin
    rxListProcDebugStatus <= 32'b0;
    rxListProcDebugAddr   <= 32'b0;
    rxListProcDebugLen    <= 32'b0;
  end
  else if (saveFrm_p)
  begin
    rxListProcDebugStatus <= rxFifoRdData;
    rxListProcDebugAddr   <= rxListStartAddress;
  end  
  else if (rxListProcCs == WAIT_WR_FRM_LEN)
  begin
    rxListProcDebugLen    <= (rxNDP) ? 32'b0 : rxFifoRdData;
  end  
end



////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 
// rxListProc FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (rxListProcCs)
        IDLE                  :  rxListProcCs_str = {"IDLE"};        
        WAIT_HDR_CS_PASSIVE   :  rxListProcCs_str = {"WAIT_HDR_CS_PASSIVE"};        
        FETCH_HDR_DESC        :  rxListProcCs_str = {"FETCH_HDR_DESC"};        
        WAIT_HDR_DESC_DONE    :  rxListProcCs_str = {"WAIT_HDR_DESC_DONE"};        
        CHK_FRM_STRT          :  rxListProcCs_str = {"CHK_FRM_STRT"};        
        MOVE_HDR_TO_MEM       :  rxListProcCs_str = {"MOVE_HDR_TO_MEM"};        
        WAIT_HDR_DONE         :  rxListProcCs_str = {"WAIT_HDR_DONE"};        
        WAIT_TH_EOP           :  rxListProcCs_str = {"WAIT_TH_EOP"};        
        WAIT_PLD_CS_PASSIVE   :  rxListProcCs_str = {"WAIT_PLD_CS_PASSIVE"};        
        UPD_CURR_PTR          :  rxListProcCs_str = {"UPD_CURR_PTR"};        
        FETCH_PLD_DESC        :  rxListProcCs_str = {"FETCH_PLD_DESC"};        
        WAIT_PLD_DESC_DONE    :  rxListProcCs_str = {"WAIT_PLD_DESC_DONE"};        
        MOVE_PLD_TO_MEM       :  rxListProcCs_str = {"MOVE_PLD_TO_MEM"};        
        WAIT_PLD_DONE         :  rxListProcCs_str = {"WAIT_PLD_DONE"};        
        WR_LAST_PLD_PTR       :  rxListProcCs_str = {"WR_LAST_PLD_PTR"};        
        WAIT_WR_LAST_PLD_PTR  :  rxListProcCs_str = {"WAIT_WR_LAST_PLD_PTR"};        
        WR_PLD_PTR_REF        :  rxListProcCs_str = {"WR_PLD_PTR_REF"};        
        WAIT_WR_PLD_PTR_REF   :  rxListProcCs_str = {"WAIT_WR_PLD_PTR_REF"};        
        WR_FRM_LEN            :  rxListProcCs_str = {"WR_FRM_LEN"};        
        WAIT_WR_FRM_LEN       :  rxListProcCs_str = {"WAIT_WR_FRM_LEN"};        
        UPD_DESC_FLDS         :  rxListProcCs_str = {"UPD_DESC_FLDS"};        
        WAIT_UPD_DESC_FLDS    :  rxListProcCs_str = {"WAIT_UPD_DESC_FLDS"};        
        UPD_STAT              :  rxListProcCs_str = {"UPD_STAT"};        
        TRIG_HDR_PASSIVE      :  rxListProcCs_str = {"TRIG_HDR_PASSIVE"};        
        TRIG_PLD_PASSIVE      :  rxListProcCs_str = {"TRIG_PLD_PASSIVE"};        
        TRIG_HDR_HALTED       :  rxListProcCs_str = {"TRIG_HDR_HALTED"};        
        TRIG_PLD_HALTED       :  rxListProcCs_str = {"TRIG_PLD_HALTED"};        
        HDR_DMA_ERROR         :  rxListProcCs_str = {"HDR_DMA_ERROR"};        
        PLD_DMA_ERROR         :  rxListProcCs_str = {"PLD_DMA_ERROR"};        
        FRM_DISCARD           :  rxListProcCs_str = {"FRM_DISCARD"};        
        WAIT_FRM_DISCARD      :  rxListProcCs_str = {"WAIT_FRM_DISCARD"};        
                     default  :  rxListProcCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Assertions
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_ASSERT_ON

property checkInterrupt;
@(posedge macPIRxClk) (rxInterrupt && saveFrm_p) |-> ##[1:$] rxTrigger;
endproperty
checkInterrupt1: assert property (checkInterrupt);

property hdrTagCheck;
@(posedge macPIRxClk) 
  ((rxListProcCs == WAIT_HDR_DONE) && (transactionSize == 1) && 
    ~rxListError && ~discardFrm_p) |-> 
                       (endHdr); 
endproperty
hdrTagCheck1: assert property (hdrTagCheck);

// property pldTagCheck;
// @(posedge macPIRxClk) endPld |-> ((rxListProcCs == WAIT_PLD_DONE) || (rxListProcCs == CHK_FRM_STRT)); 
// endproperty
// pldTagCheck1: assert property (pldTagCheck);

property saveFrmCheck;
@(posedge macPIRxClk) 
  disable iff(macPIRxClkHardRst_n==0) 
  saveFrm_p |-> ((rxListProcCs == WAIT_UPD_DESC_FLDS) && 
                                    (remainingData == 16'b1));
endproperty
saveFrmCheck1: assert property (saveFrmCheck);
`endif

endmodule