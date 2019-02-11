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
// Description      : This module is the Primary Controller for the DMA in the 
//                    TX mode. 
// Simulation Notes : System verilog assertions can be enabled with RW_ASSERT_ON
//                    Then a system verilog capable simulator is needed
// Synthesis Notes  : 
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements : When the newHead bit is set the FSM
//                    immediately moves to HALTED. This is not in accordance
//                    to the behavior specified in UM. This should be changed
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module txPrimCtrl (
          //Port Definitions

          //$port_g Clock and reset interface
          input wire         macPITxClk,          //Platform 1 Clk domain
          input wire         macPITxClkHardRst_n, //Hard Reset Synchronized to macPITxClk
          input wire         macPITxClkSoftRst_n, //Soft Reset synchronized to macPITxClk

          //$port_g TxListProcessor interface
          input wire         trigTxPCHalt_p,      //trigger from TxListProcessor to move FSM to HALTED
          input wire         trigTxPCDead_p,      //trigger from TxListProcessor to move FSM to DEAD
          input wire         trigTxPCActive,      //trigger from MAC Controller to move FSM to ACTIVE
          input wire         txStateActiveMC,     //mask the pcTrigTxListProc from resync in the wrapper
          input wire         txNewTail,           //Indicates New tail bit is set
          input wire         nxtAtomFrmPtrValid,  //Indicates the validity of the next Atomic Frame Pointer
          input wire         nxtMpduDescPtrValid, //Indicates the validity of the next Mpdu Descriptor Pointer
          input wire         txNewHead,           //Indicates new Head pointer is set
          input wire         haltAfterTxop,       //if set FSM moves to HALTED after endOfTxop
          input wire         updPCStaPtr_p,       //Update the PC Status Pointer signal.
          input wire [31:0]  txHeadPtr,           //Queue Head Pointer
          input wire [31:0]  nxtDescPtr,          //the next Descriptor Pointer to be updated to
          output wire        pcTrigTxListProc,    //Trigger for the Tx List Processor
          output wire        rstNewHead_p,        //Reset New Head bit.
          output wire        rstNewTail_p,        //Reset New Tail bit.
          output reg  [31:0] pcStatusPtr,         //The status pointer
          output wire        txNewHeadErr,        // Transmit New Head Error
          output reg         txStartup,           // Transmit Startup      
          output reg         txEndQ,              // Transmit  End of Queue  
          output reg         txHaltAfterTXOP,     // Transmit Halt After TXOP        
          output reg         txDMADead,           // Transmit Channel error

          //$port_g Debug interface
          output wire [3:0]  txDmaPCState          //Debug Signal
         ); 
 

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// txPrimCtrl FSM states definition
//$fsm_sd txPrimCtrlCs
localparam 
           HALTED  =  4'd1, // Reset state and SW not yet ready state
           PASSIVE =  4'd2, // Waiting for the trigger from the MAC Controller
           ACTIVE  =  4'd4, // Currently performing a dma transfer.
           DEAD    =  4'd8; // Error state. 

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

//Internal Signal Definitions
//Registers
reg [3:0]  txPrimCtrlCs;
reg [3:0]  txPrimCtrlNs;


//Wires
//The Queue head Pointer is valid
wire        txHeadPtrValid;


`ifdef RW_SIMU_ON
// String definition to display txPrimCtrlCs current state
reg [7*8:0] txPrimCtrlCs_str;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

//Current State Logic 
always @ (posedge macPITxClk or negedge macPITxClkHardRst_n) 
begin
  if (macPITxClkHardRst_n == 1'b0)
    txPrimCtrlCs <= HALTED; 
  else if (macPITxClkSoftRst_n == 1'b0)
    txPrimCtrlCs <= HALTED;
  else
    txPrimCtrlCs <= txPrimCtrlNs; 
end


assign txHeadPtrValid = ( (txHeadPtr[1:0] == 2'b00) && (txHeadPtr[31:2] != 30'b0) ) ? 1'b1 : 1'b0 ;


//Next state Logic.
always @* 
begin
  case(txPrimCtrlCs)

    HALTED:
      //$fsm_s The state machine starts up in this state after reset. 
      //It may also transition to this state under other conditions. 
      //In this state, the state machine waits for the txNewTail or txNewHead bits to be asserted.
      if (txNewTail == 1'b1 ||
         (txNewHead == 1'b1 && txHeadPtrValid == 1'b1)) 
        //$fsm_t If the new head bit is set the header pointer 
        //valid bit should also be set. These are set by the SW when
        //it has the data prepared and queued in the Local SRAM
        txPrimCtrlNs = PASSIVE; 
      else if (txNewHead == 1'b1 && txHeadPtrValid == 1'b0)
        //$fsm_t If a newHead indication is received but the Head Pointer 
        //is not valid, the FSM moves to DEAD
        txPrimCtrlNs = DEAD; 
      else
        //$fsm_t If nothing happens, the FSM stays in HALTED
        txPrimCtrlNs = HALTED;

    PASSIVE:
      //$fsm_s FSM waits in this state until the MAC Controller gives 
      //a trigger. this trigger indicates to the DMA to start
      //moving the frames from the Local SRAM to the TX FIFO for
      //the MAC Controller to transmit the frame. The MAC Controller
      //gives this trigger when it is likely to get the TXOP
      //pcStatusPtr is updated to corresponding txHeadPtr when the txHeadPtrValid is asserted.
      if (txNewHead == 1'b1 || haltAfterTxop)
        //$fsm_t If the newHead bit is set at any time the FSM should move 
        //to HALTED. This is normally not set by the SW and the SW 
        //should set it only to reset the system or so on
        txPrimCtrlNs = HALTED;
      else if (trigTxPCActive == 1'b1)
        //$fsm_t If trigTxPCActive is asserted by the MAC Controller,
        //the FSM moves to ACTIVE to start the Transmit DMA operations.
        txPrimCtrlNs = ACTIVE;
      else 
        //$fsm_t If nothing happens, the FSM stays in PASSIVE
        txPrimCtrlNs = PASSIVE;
  
  
  
    ACTIVE:
      //$fsm_s In this state the DMA triggers the Transmit List Processor
      //to start moving the frames from the Local SRAM to the TX FIFO 
      // When Transmit List Processor asserts the updPCStaPtr_p, the value on nextDescPtr is copied to the pcStatusPtr.
      if (trigTxPCDead_p == 1'b1)
        //$fsm_t The FSM will move to DEAD if its triggered by the TxListProcessor
        //to do so.This might happen in cases of error like policy table 
        //invalid, dmaHIF bus transaction error.   
        txPrimCtrlNs = DEAD;

      else if (txNewHead == 1'b1 ||
               trigTxPCHalt_p == 1'b1 ||
              (trigTxPCActive == 1'b0 && haltAfterTxop == 1'b1))
        //$fsm_t If the txNewHead bit is set and the FSM is not in HALTED it 
        //moves to HALTED and begins operations afresh
        txPrimCtrlNs = HALTED;
      else if (trigTxPCActive == 1'b0 && haltAfterTxop == 1'b0)
        //$fsm_t If there is a stopDMA indication from the MAC Controller then
        //the FSM moves to PASSIVE
        txPrimCtrlNs = PASSIVE;
      else
        //$fsm_t If nothing happens, the FSM stays in ACTIVE
        txPrimCtrlNs = ACTIVE;

    DEAD:
      //$fsm_s In this state, the state machine waits for error recovery from SW. 
      //The FSM enters in this state when there is an error encountered
      //during the operation of the DMA like a policy table error or
      //a dmaHIF bus transaction error. Error recovery is only by SW which
      //is a system level reset 
      
      //$fsm_t Only the SW can recover the FSM from this state using SW reset
      txPrimCtrlNs = DEAD;
   
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:
      txPrimCtrlNs = HALTED;
    // pragma coverage block = on 
  endcase
end 


always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txDMADead <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txDMADead <= 1'b0;
  else if (((txPrimCtrlCs == ACTIVE) && trigTxPCDead_p) || 
           ((txPrimCtrlCs == HALTED) && (txNewHead == 1'b1 && txHeadPtrValid == 1'b0))) 
    txDMADead <= 1'b1;
  else 
    txDMADead <= 1'b0;
end

//Logic for txStartup
//The txStartup is reset when the DMA channel leaves the HALTED state 
//for the PASSIVE or ACTIVE.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txStartup <= 1'b1;
  else if (macPITxClkSoftRst_n == 1'b0)
    txStartup <= 1'b1; 
  else if ((txPrimCtrlCs == ACTIVE) || (txPrimCtrlCs == PASSIVE))
    txStartup <= 1'b0; 
end    

//Logic for txEndQ
//The txEndQ is set when the DMA channel moves in HALTED state 
//because it reaches the end of the linked list
//The txEndQ is reset when the DMA channel leaves the HALTED state 
//for the PASSIVE or ACTIVE.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txEndQ <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txEndQ <= 1'b0; 
  else if (trigTxPCHalt_p)
    txEndQ <= 1'b1; 
  else if ((txPrimCtrlCs == ACTIVE) || (txPrimCtrlCs == PASSIVE))
    txEndQ <= 1'b0; 
end    

//Logic for txHaltAfterTXOP
//The txHaltAfterTXOP is set when the DMA channel moves in HALTED state 
//because it reaches the end of the TX OP
//The txHaltAfterTXOP is reset when the DMA channel leaves the HALTED state 
//for the PASSIVE or ACTIVE.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txHaltAfterTXOP <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txHaltAfterTXOP <= 1'b0; 
  else if (trigTxPCActive == 1'b0 && haltAfterTxop == 1'b1)
    txHaltAfterTXOP <= 1'b1; 
  else if ((txPrimCtrlCs == ACTIVE) || (txPrimCtrlCs == PASSIVE))
    txHaltAfterTXOP <= 1'b0; 
end    

//Logic for Status Pointer
//The status pointer takes the new head pointer in the 
//register when the new head bit is set and the FSM is 
//in HALTED. 
//It updates to the nextDescriptorPointer given by the 
//status updater when it is triggered by the same.
//The Status updater will trigger for the updation after
//it has completed writing the status info to the descriptor
//In case of New tail bit being set the existing status pointer
//is the starting point for fetching the descriptors
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    pcStatusPtr <= 32'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    pcStatusPtr <= 32'b0; 
  else if (txHeadPtrValid == 1'b1 &&
           txNewHead == 1'b1 && 
           txPrimCtrlCs == HALTED)
    pcStatusPtr <= txHeadPtr;
  else if (updPCStaPtr_p == 1'b1)
    pcStatusPtr <= nxtDescPtr;
end    


//Logic for pcTrigTxListProc 
//This indicates to the Transmit list Processor this particular
//channel is in ACTIVE state
assign pcTrigTxListProc = ((txPrimCtrlCs == ACTIVE) && (txStateActiveMC == 1'b1)) ? 1'b1 : 1'b0;

//This signal resets the newHead bit after the new Head has been read
//This signal is asserted each time when the FSM moves from the HALTED
//state and the txNewHead is high and txHeadPtrValid bit is high. This 
//means that the FSM has samples the txNewHead bit. This signal is 
//generated only in the HALTED state 
assign rstNewHead_p = (txPrimCtrlCs == HALTED && 
                       txNewHead == 1'b1 &&
                       txHeadPtrValid == 1'b1)
                       ? 1'b1 : 1'b0; 

//This signal resets the newTail bit after the newTail has been read
assign rstNewTail_p = (txNewTail == 1'b1 &&
                      (txPrimCtrlCs == HALTED ||
                       txPrimCtrlCs == PASSIVE ||
                      (txPrimCtrlCs == ACTIVE &&
                      (nxtAtomFrmPtrValid == 1'b1 ||
                       nxtMpduDescPtrValid == 1'b1))))                       
                       ? 1'b1 : 1'b0;

//This signal gives the present state of the Transmit Primary Controller
assign txDmaPCState = txPrimCtrlCs;

// Indicates that the Transmit DMA channel's newHead bit was set but the 
// queueHeadPointer did not have a valid address.
assign txNewHeadErr = txNewHead & !txHeadPtrValid;

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
  case (txPrimCtrlCs)
        HALTED                :  txPrimCtrlCs_str = {"HALTED"};        
        PASSIVE               :  txPrimCtrlCs_str = {"PASSIVE"};        
        ACTIVE                :  txPrimCtrlCs_str = {"ACTIVE"};        
        DEAD                  :  txPrimCtrlCs_str = {"DEAD"};        
                     default  :  txPrimCtrlCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON


`ifdef RW_ASSERT_ON
//Checks if trigger to DEAD happens only in ACTIVE state
property deadTrigger;
disable iff (!macPITxClkHardRst_n)
@(posedge trigTxPCDead_p) ((txPrimCtrlCs != PASSIVE) && (txPrimCtrlCs != HALTED)); 
endproperty
deadTriggrdRongState: assert property (deadTrigger); 

//Checks if the txNewHead bit from the csReg module is resetted correctly
property immediateFellCheck(clk,inp1,inp2);
disable iff (!macPITxClkHardRst_n)
@(posedge clk) $rose(inp1) |-> ##1 (!inp2);
endproperty

inputNewHeadCheck: assert property(immediateFellCheck(macPITxClk,rstNewHead_p,txNewHead));
inputNewTailCheck: assert property(immediateFellCheck(macPITxClk,rstNewTail_p,txNewTail));
`endif                      


endmodule
