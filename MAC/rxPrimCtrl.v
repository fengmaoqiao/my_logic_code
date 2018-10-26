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
//                    RX mode
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

module rxPrimCtrl (
         //Port Definitions
         //$port_g Clock and reset interface
         input wire         macPIRxClk, //Synchronized to Platform 2 clock
         input wire         macPIRxClkHardRst_n, //Hard Reset synchronized to macPIRxClk
         input wire         macPIRxClkSoftRst_n, //Soft Reset synchronized to macPIRxClk

         //$port_g Receive List Processor interface
         input wire         trigHalt_p,   //From Receive List Processor to move FSM to HALTED
         input wire         trigPassive_p,//From Receive List Processor to move FSM to PASSIVE
         input wire         trigActive_p, //From Receive List Processor to move FSM to ACTIVE
         input wire         trigDead_p,   //From Receive List Processor to move FSM to DEAD

         //$port_g CSReg interface
         input wire         rxNewTail,    //From csReg. Indicates if new tail bit is set
         input wire         rxNewHead,    //From csReg. Indicates if new head bit is set
         input wire         updStaPtr_p,  //From the receive list processor. Indicates to update the status pointer
         input wire  [31:0] rxHeadPtr,    //The receive queue head pointer
         input wire  [31:0] nxtDescPtr,   //The next descriptor pointer from the descriptor
         output wire        rstNewTail,   //Resets the new tail bit
         output wire        rstNewHead,   //Resets the new head bit
         output reg  [31:0] statusPtr,    //Indicates the status Pointer for this channel
         output reg         rxNewHeadErr, // Receive New Head Error
         output reg         rxDMADead,    // Receive Channel error
         output wire  [3:0] rxDmaPCState  //Indicates the current Status of FSM.Connected to csReg block
                   );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
// rxPrimCtrl FSM states definition
//$fsm_sd rxPrimCtrl
localparam 
           HALTED  = 4'd1, //Waiting for SW to chain descriptors
           PASSIVE = 4'd2, //Waiting for frame reception
           ACTIVE  = 4'd4, //Active Frame receptions
           DEAD    = 4'd8; //Error during reception in the DMA


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
//Internal Register declarations
reg  [3:0] rxPrimCtrlCs; //Current state register
reg  [3:0] rxPrimCtrlNs; //Next State register

//Internal Wire declarations
wire       nxtDescPtrValid; //Indicates the next descriptor ptr is valid
wire       rxHeadPtrValid; //Is asserted when the receive head pointer is valid


`ifdef RW_SIMU_ON
// String definition to display rxPrimCtrlCs current state
reg [7*8:0] rxPrimCtrlCs_str;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


//Logic for current state
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxPrimCtrlCs <= HALTED;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxPrimCtrlCs <= HALTED;
  else
    rxPrimCtrlCs <= rxPrimCtrlNs;
end

//Logic for nextState
always @*
begin
  case(rxPrimCtrlCs)
    
    HALTED:
      //$fsm_s The state machine starts up in this state after reset. 
      //It may also transition to this state under other conditions. 
      //In this state, the state machine waits for the rxNewTail or rxNewHead signals to be asserted. 
      if (rxNewTail == 1'b1 ||
         (rxNewHead == 1'b1 &&
          rxHeadPtrValid == 1'b1))
        //$fsm_t Move to PASSIVE when the new Tail bit is set
        //or when the new head bit is set and the queue head 
        //pointer is valid.These information are set by SW
        //they are set when the descriptors are ready for 
        //moving in data from the RX FIFO to the Local SRAM
        rxPrimCtrlNs = PASSIVE;
      else if ((rxNewHead == 1'b1) && (rxHeadPtrValid == 1'b0))
        //$fsm_t If a newHead indication is received but the Head Pointer 
        //is not valid, the FSM moves to DEAD
        rxPrimCtrlNs = DEAD;
      else
        //$fsm_t If nothing happens, the FSM stays in HALTED
        rxPrimCtrlNs = HALTED; 

    PASSIVE:
      //$fsm_s In this state, the HW waits for a trigger from the Receive List Processor to start the DMA operations.
      if (rxNewHead == 1'b1) 
        //$fsm_t FSM moves to halted on trigger from receive
        //list processor or when a new head bit is set
        rxPrimCtrlNs = HALTED;
      else if (trigActive_p == 1'b1)
        //$fsm_t moves to active on a trigger from receive 
        //list processor
        rxPrimCtrlNs = ACTIVE;
      else 
        //$fsm_t If nothing happens, the FSM stays in PASSIVE
        rxPrimCtrlNs = PASSIVE;

    ACTIVE:
      //$fsm_s FSM remains in this state until Receive List Processor asserts trigHalt_p 
      // (when next descriptor pointer is not valid) or trigPassive_p or trigDead_p 
      // (when DMA error occurs).
      if (trigDead_p == 1'b1)
        //$fsm_t moves to DEAD on a trigger from receive
        //list processor
        rxPrimCtrlNs = DEAD;
      else if (trigHalt_p == 1'b1 ||
              (updStaPtr_p == 1'b1 && 
               rxNewHead == 1'b1))
        //$fsm_t moves to HALTED either on a trigger from
        //rx List processor or when a new head bit
        // is set
        rxPrimCtrlNs = HALTED;
      else if (trigPassive_p == 1'b1)
        //$fsm_t goes to PASSIVE on a trigger from receive
        //list processor. this  occurs when the 
        //reception is over
        rxPrimCtrlNs = PASSIVE;
      else
        //$fsm_t If nothing happens, the FSM stays in ACTIVE
        rxPrimCtrlNs = ACTIVE;

    DEAD: 
      //$fsm_s In this state, the state machine waits for error recovery from SW. 
      //The FSM enters in this state when there is an error encountered
      //during the operation of the DMA like a policy table error or
      //a dmaHIF bus transaction error. Error recovery is only by SW which
      //is a system level reset 
      
      //$fsm_t Only the SW can recover the FSM from this state using SW reset
      rxPrimCtrlNs = DEAD;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:
      rxPrimCtrlNs = HALTED;
    // pragma coverage block = on 
  endcase
end


always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxDMADead <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxDMADead <= 1'b0;
  else if (((rxPrimCtrlCs == ACTIVE) && trigDead_p) || 
           ((rxPrimCtrlCs == HALTED) && (rxNewHead == 1'b1) && (rxHeadPtrValid == 1'b0))) 
    rxDMADead <= 1'b1;
  else 
    rxDMADead <= 1'b0;
end

//logic for statusPtr
//The statusPointer is maintained and initialized in this
//block. the control and manipulation of the status pointer
//rests with the rx list processor. the status pointer is 
//updated on a trigger from the receive list processor to
//the next descriptor pointer passed by the receive list
//processor. it gets initialized to the queue head poitner
//when in HALTED and newHead is set and the queue head pointer
// is valid
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    statusPtr <= 32'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    statusPtr <= 32'b0;
  else if (rxPrimCtrlCs == HALTED &&
           rxNewHead == 1'b1 &&
           rxHeadPtrValid == 1'b1) 
    statusPtr <= rxHeadPtr;
  else if (updStaPtr_p == 1'b1 && nxtDescPtrValid == 1'b1)
    statusPtr <= nxtDescPtr;
end

//Receive queue head pointer validity
assign rxHeadPtrValid  = ((rxHeadPtr[1:0] == 2'b00)  && (rxHeadPtr  != 0)) ? 1'b1 : 1'b0;

assign nxtDescPtrValid = ((nxtDescPtr[1:0] == 2'b00) && (nxtDescPtr != 0)) ? 1'b1 : 1'b0;

//Resets the new tail bit 
//This signal is asserted whenever the FSM moves
//from HALTED and the rxNewTail bit is set. This 
//means the 
assign rstNewTail = ((rxPrimCtrlCs == HALTED  || 
                      rxPrimCtrlCs == PASSIVE ||
                     (rxPrimCtrlCs == ACTIVE &&
                      nxtDescPtrValid == 1'b1)) &&
                      rxNewTail == 1'b1);

//Resets the new head bit
//This signal is asserted whenever the FSM moves from
//HALTED and the rxNewHead bit is set. This means 
//the rxNewHead is sampled
assign rstNewHead = (rxPrimCtrlCs == HALTED &&
                     rxNewHead == 1'b1 &&
                     rxHeadPtrValid == 1'b1);

//This signal gives the present state of the RX Primary
//Controller FSM
assign rxDmaPCState = rxPrimCtrlCs;


//Indication when a rxNewHead has been requested with invalid rxHeadPtr
always @(posedge macPIRxClk or negedge macPIRxClkHardRst_n)
begin
  if (macPIRxClkHardRst_n == 1'b0)
    rxNewHeadErr <= 1'b0;
  else if (macPIRxClkSoftRst_n == 1'b0)
    rxNewHeadErr <= 1'b0;
  else if ((rxNewHead == 1'b1) && (rxHeadPtrValid == 1'b0))
    rxNewHeadErr <= 1'b1;
end

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
  case (rxPrimCtrlCs)
        HALTED    :  rxPrimCtrlCs_str = {"HALTED"};        
        PASSIVE   :  rxPrimCtrlCs_str = {"PASSIVE"};        
        ACTIVE    :  rxPrimCtrlCs_str = {"ACTIVE"};        
        DEAD      :  rxPrimCtrlCs_str = {"DEAD"};        
        default   :  rxPrimCtrlCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

`ifdef RW_ASSERT_ON
//Checks if trigger to DEAD happens only in ACTIVE state
property deadTrigger;
@(posedge macPIRxClk) ((rxPrimCtrlCs == PASSIVE) || (rxPrimCtrlCs == HALTED)) |->
                     !trigDead_p;
endproperty
deadTriggrdRongState: assert property (deadTrigger);

//Checks if the txNewHead bit from the csReg module is resetted correctly
property immediateFellCheck(clk,inp1,inp2);
@(posedge clk) $rose(inp1) |-> ##1 (!inp2);
endproperty

inputNewHeadCheck: assert property(immediateFellCheck(macPIRxClk,rstNewHead,rxNewHead));
inputNewTailCheck: assert property(immediateFellCheck(macPIRxClk,rstNewTail,rxNewTail));
`endif


endmodule
                     
