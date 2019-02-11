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
// Description      : This block implements the Selection logic for the signals
//                    between the Primary Controller and the Transmit List 
//                    processor
// Simulation Notes : 
// Synthesis Notes  : 
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms && concepts :                                                       
// Bugs             :                                                       
// Open issues and future enhancements :                                    
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////

module txPrimCtrlSelLogic (
          //$port_g Clock and reset interface
          input wire         macPITxClk,         //Platform 1 Clk domain
          input wire         macPITxClkHardRst_n,//Hard Reset Synchronized to macPITxClk
          input wire         macPITxClkSoftRst_n,//Soft Reset synchronized to macPITxClk

          //$port_g TxList Proc interface 
          input wire         trigHalt_p,           //From TxList Proc. Triggers PrimCtrl FSM to HALTED

          input wire         trigDead_p,           //From TxList Proc. Triggers PrimCtrl FSM to DEAD

          input wire         underRunDetected_p,   //From MAC Controller. Indicates a frame Lenght mismatch
                                                   //and the active channel has to be triggered to DEAD  

          input wire         patternError,         //From TxList Proc. 
          input wire         dmaHIFError,          //From dmaHIF Master. Indicates during transacation there was an
                                                   //dmaHIF error response
          
          input wire         nxtAtomFrmPtrValid,   //From TxList Proc. Indicates the nextAtomic Frame Pointer is valid
          input wire         nxtMpduDescValid,     //From TxList Proc. Indicates the next MPDU Descriptor Pointer is valid

          //$port_g Primary Ctlr interface 
          input wire  [31:0] bcnStatusPointer,     //Beacon Status Pointer.
          input wire         bcnTrigTxListProc,    //Trig for TxListProc from the Beacon Primary Ctlr.

          input wire  [31:0] ac0StatusPointer,     //AC0 Status Pointer.
          input wire         ac0TrigTxListProc,    //Trig for TxListProc from the ACO Primary Ctlr.

          input wire  [31:0] ac1StatusPointer,     //AC1 Status Pointer.
          input wire         ac1TrigTxListProc,    //Trig for TxListProc from the AC1 Primary Ctlr.

          input wire  [31:0] ac2StatusPointer,     //AC2 Status Pointer.
          input wire         ac2TrigTxListProc,    //Trig for TxListProc from the AC2 Primary Ctlr.

          input wire  [31:0] ac3StatusPointer,     //AC3 Status Pointer
          input wire         ac3TrigTxListProc,    //Trig for TxListProc from the AC3 Primary Ctlr.

          input wire         plyTblValid,          //Indicates validity of policy table address

          output reg  [31:0] statusPointer,        //multiplexed Status Pointer for the Active Chan.
          output wire        trigTxListProc,       //multiplexed Trigger for the Active Chan.

          output wire        trigBcnHalt_p,        //Demultiplexed Halt trigger for the Beacon Channel
          output wire        trigBcnDead_p,        //Demultiplexed Dead trigger for the Beacon Channel
          output wire        nxtAtomFrmPtrValidBcn,//Next Atomic Frame Pointer Valid indication for Beacon Channel
          output wire        nxtMpduDescValidBcn,  //Next Mpdu descriptor Pointer Valid indication for Beacon Channel

          output wire        trigAc0Halt_p,        //Demultiplexed Halt trigger for the AC0 Channel
          output wire        trigAc0Dead_p,        //Demultiplexed Dead trigger for the AC0 Channel
          output wire        nxtAtomFrmPtrValidAc0,//Next Atomic Frame Pointer Valid indication for AC0 Channel
          output wire        nxtMpduDescValidAc0,  //Next Mpdu descriptor Pointer Valid indication for AC0 Channel

          output wire        trigAc1Halt_p,        //Demultiplexed Halt trigger for the AC1 Channel
          output wire        trigAc1Dead_p,        //Demultiplexed Dead trigger for the AC1 Channel
          output wire        nxtAtomFrmPtrValidAc1,//Next Atomic Frame Pointer Valid indication for AC1 Channel
          output wire        nxtMpduDescValidAc1,  //Next Mpdu descriptor Pointer Valid indication for AC1 Channel

          output wire        trigAc2Halt_p,        //Demultiplexed Halt trigger for the AC2 Channel
          output wire        trigAc2Dead_p,        //Demultiplexed Dead trigger for the AC2 Channel
          output wire        nxtAtomFrmPtrValidAc2,//Next Atomic Frame Pointer Valid indication for AC2 Channel
          output wire        nxtMpduDescValidAc2,  //Next Mpdu descriptor Pointer Valid indication for AC2 Channel

          output wire        trigAc3Halt_p,        //Demultiplexed Halt trigger for the AC3 Channel
          output wire        trigAc3Dead_p,        //Demultiplexed Dead trigger for the AC3 Channel
          output wire        nxtAtomFrmPtrValidAc3,//Next Atomic Frame Pointer Valid indication for AC3 Channel
          output wire        nxtMpduDescValidAc3,  //Next Mpdu descriptor Pointer Valid indication for AC3 Channel

          //$port_g Status Registers indication
          output reg         txBcnLenMismatch,     // Transmit Beacon Length Mismatch
          output reg         txAC0LenMismatch,     // Transmit AC0 Length Mismatch
          output reg         txAC1LenMismatch,     // Transmit AC1 Length Mismatch
          output reg         txAC2LenMismatch,     // Transmit AC2 Length Mismatch
          output reg         txAC3LenMismatch,     // Transmit AC3 Length Mismatch
          output reg         txBcnUPatternErr,     // Transmit Beacon Unique Pattern Error
          output reg         txAC0UPatternErr,     // Transmit AC0 Unique Pattern Error
          output reg         txAC1UPatternErr,     // Transmit AC1 Unique Pattern Error
          output reg         txAC2UPatternErr,     // Transmit AC2 Unique Pattern Error
          output reg         txAC3UPatternErr,     // Transmit AC3 Unique Pattern Error
          output reg         txBcnNextPointerErr,  // Transmit Beacon Next Pointer Error
          output reg         txAC0NextPointerErr,  // Transmit AC0 Next Pointer Error
          output reg         txAC1NextPointerErr,  // Transmit AC1 Next Pointer Error
          output reg         txAC2NextPointerErr,  // Transmit AC2 Next Pointer Error
          output reg         txAC3NextPointerErr,  // Transmit AC3 Next Pointer Error
          output reg         txBcnPTAddressErr,    // Transmit Beacon Policy Table Address Error
          output reg         txAC0PTAddressErr,    // Transmit AC0 Policy Table Address Error
          output reg         txAC1PTAddressErr,    // Transmit AC1 Policy Table Address Error
          output reg         txAC2PTAddressErr,    // Transmit AC2 Policy Table Address Error
          output reg         txAC3PTAddressErr,    // Transmit AC3 Policy Table Address Error
          output reg         txBcnBusErr,          // Transmit Beacon Bus Error
          output reg         txAC0BusErr,          // Transmit AC0 Bus Error
          output reg         txAC1BusErr,          // Transmit AC1 Bus Error
          output reg         txAC2BusErr,          // Transmit AC2 Bus Error
          output reg         txAC3BusErr           // Transmit AC3 Bus Error
           
         ); 

localparam BEACON = 5'b10000,//Multiplexes signals for the beacon prim ctlr
           AC0    = 5'b01000,//Multiplexes signals for the AC0 prim ctlr
           AC1    = 5'b00100,//Multiplexes signals for the AC1 prim ctlr
           AC2    = 5'b00010,//Multiplexes signals for the AC2 prim ctlr
           AC3    = 5'b00001;//Multiplexes signals for the AC3 prim ctlr


//Internal Signal Declarations
reg   [4:0] selectSignal;
reg         trigTxListProcDly;

//Logic for selectSignal.
//The selectSignal is generated based on the trigger for the Trnasmit List
//Processor given by the Transmit Primary Controller. And since only one 
//primary controller can be active the selectSignal is just given as a 
//concatenation of all the trigger signals. And all the trigger signals are 
//asserted high and are not pulses. So through the entire transfer when the
//channel is active the selectSignal will point to the correct Primary 
//Controller.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    selectSignal <= 5'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    selectSignal <= 5'b0;
  else if (trigTxListProc && !trigTxListProcDly)
    selectSignal <= {bcnTrigTxListProc, ac0TrigTxListProc, ac1TrigTxListProc, 
                     ac2TrigTxListProc, ac3TrigTxListProc};
end

//trigTxListProc Delayedof 1 clock cycle. Used to detect the rising edge of trigTxListProc. 
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    trigTxListProcDly <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    trigTxListProcDly <= 1'b0;
  else 
    trigTxListProcDly <= trigTxListProc;
end


//When the Beacon channel is active as indicated by the bcnTrigTxListProc
//asserted HIGH the trigHalt_p is routed to the Beacon channel
assign trigBcnHalt_p        = trigHalt_p   && bcnTrigTxListProc;

//When the Beacon channel is active as indicated by the bcnTrigTxListProc
//asserted HIGH the trigDead_p is routed to the Beacon channel
assign trigBcnDead_p        = trigDead_p   && bcnTrigTxListProc;

//When the AC0 channel is active as indicated by the ac0TrigTxListProc
//asserted HIGH the trigHalt_p is routed to the AC0 channel
assign trigAc0Halt_p        = trigHalt_p   && ac0TrigTxListProc;

//When the AC0 channel is active as indicated by the ac0TrigTxListProc
//asserted HIGH the trigDead_p is routed to the AC0 channel
assign trigAc0Dead_p        = trigDead_p   && ac0TrigTxListProc;

//When the AC1 channel is active as indicated by the ac1TrigTxListProc
//asserted HIGH the trigHalt_p is routed to the AC1 channel
assign trigAc1Halt_p        = trigHalt_p   && ac1TrigTxListProc;

//When the AC1 channel is active as indicated by the ac1TrigTxListProc
//asserted HIGH the trigDead_p is routed to the AC1 channel
assign trigAc1Dead_p        = trigDead_p   && ac1TrigTxListProc;

//When the AC2 channel is active as indicated by the ac2TrigTxListProc
//asserted HIGH the trigHalt_p is routed to the AC2 channel
assign trigAc2Halt_p        = trigHalt_p   && ac2TrigTxListProc;

//When the AC2 channel is active as indicated by the ac2TrigTxListProc
//asserted HIGH the trigDead_p is routed to the AC2 channel
assign trigAc2Dead_p        = trigDead_p   && ac2TrigTxListProc;

//When the AC3 channel is active as indicated by the ac3TrigTxListProc
//asserted HIGH the trigHalt_p is routed to the AC3 channel
assign trigAc3Halt_p        = trigHalt_p   && ac3TrigTxListProc;

//When the AC3 channel is active as indicated by the ac3TrigTxListProc
//asserted HIGH the trigDead_p is routed to the AC3 channel
assign trigAc3Dead_p        = trigDead_p   && ac3TrigTxListProc;

//The multiplexed trigger for the transmit list processor from different 
//channels is generated
assign trigTxListProc = bcnTrigTxListProc || ac0TrigTxListProc ||
                        ac1TrigTxListProc || ac2TrigTxListProc ||
                        ac3TrigTxListProc;

//Assigning the nxtAtomFrmPtrValid to the ACTIVE primary controller
assign nxtAtomFrmPtrValidAc0 = nxtAtomFrmPtrValid && ac0TrigTxListProc;

//Assigning the nxtAtomFrmPtrValid to the ACTIVE primary controller
assign nxtAtomFrmPtrValidAc1 = nxtAtomFrmPtrValid && ac1TrigTxListProc;

//Assigning the nxtAtomFrmPtrValid to the ACTIVE primary controller
assign nxtAtomFrmPtrValidAc2 = nxtAtomFrmPtrValid && ac2TrigTxListProc;

//Assigning the nxtAtomFrmPtrValid to the ACTIVE primary controller
assign nxtAtomFrmPtrValidAc3 = nxtAtomFrmPtrValid && ac3TrigTxListProc;

//Assigning the nxtAtomFrmPtrValid to the ACTIVE primary controller
assign nxtAtomFrmPtrValidBcn = nxtAtomFrmPtrValid && bcnTrigTxListProc;

//Assigning the nxtMpduDescValid to the ACTIVE primary controller
assign nxtMpduDescValidAc0 = nxtMpduDescValid && ac0TrigTxListProc;

//Assigning the nxtMpduDescValid to the ACTIVE primary controller
assign nxtMpduDescValidAc1 = nxtMpduDescValid && ac1TrigTxListProc;

//Assigning the nxtMpduDescValid to the ACTIVE primary controller
assign nxtMpduDescValidAc2 = nxtMpduDescValid && ac2TrigTxListProc;

//Assigning the nxtMpduDescValid to the ACTIVE primary controller
assign nxtMpduDescValidAc3 = nxtMpduDescValid && ac3TrigTxListProc;

//Assigning the nxtMpduDescValid to the ACTIVE primary controller
assign nxtMpduDescValidBcn = nxtMpduDescValid && bcnTrigTxListProc;


//Multiplexer
//This logic helps in multiplexing the status Pointer signals from 
//the different Transmit Primary Controllers to the Transmit List processor
//depending on which transmit primary controlleris currently active.
//The selection is based on the selectSignal.
always @*
begin
  case (selectSignal)
    BEACON:  statusPointer = bcnStatusPointer;
    AC0:     statusPointer = ac0StatusPointer;
    AC1:     statusPointer = ac1StatusPointer;
    AC2:     statusPointer = ac2StatusPointer;
    AC3:     statusPointer = ac3StatusPointer;
    default: statusPointer = 32'b0;
  endcase
end


//Indication to the DMA Status2 Register when an underrun is detected on BCN Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txBcnLenMismatch <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txBcnLenMismatch <= 1'b0;
  else if (underRunDetected_p && bcnTrigTxListProc)
    txBcnLenMismatch <= 1'b1;
end

//Indication to the DMA Status2 Register when an underrun is detected on AC0 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC0LenMismatch <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC0LenMismatch <= 1'b0;
  else if (underRunDetected_p && ac0TrigTxListProc)
    txAC0LenMismatch <= 1'b1;
end

//Indication to the DMA Status2 Register when an underrun is detected on AC1 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC1LenMismatch <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC1LenMismatch <= 1'b0;
  else if (underRunDetected_p && ac1TrigTxListProc)
    txAC1LenMismatch <= 1'b1;
end

//Indication to the DMA Status2 Register when an underrun is detected on AC2 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC2LenMismatch <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC2LenMismatch <= 1'b0;
  else if (underRunDetected_p && ac2TrigTxListProc)
    txAC2LenMismatch <= 1'b1;
end

//Indication to the DMA Status2 Register when an underrun is detected on AC3 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC3LenMismatch <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC3LenMismatch <= 1'b0;
  else if (underRunDetected_p && ac3TrigTxListProc)
    txAC3LenMismatch <= 1'b1;
end


// // Indication to the DMA Status2 Register when a pattern Error is detected
// assign txBcnUPatternErr  = patternError && bcnTrigTxListProc;
// assign txAC0UPatternErr  = patternError && ac0TrigTxListProc;
// assign txAC1UPatternErr  = patternError && ac1TrigTxListProc;
// assign txAC2UPatternErr  = patternError && ac2TrigTxListProc;
// assign txAC3UPatternErr  = patternError && ac3TrigTxListProc;
// Indication to the DMA Status2 Register when a pattern Error is detected on BCN Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txBcnUPatternErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txBcnUPatternErr <= 1'b0;
  else if (patternError && bcnTrigTxListProc && trigDead_p)
    txBcnUPatternErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a pattern Error is detected on AC0 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC0UPatternErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC0UPatternErr <= 1'b0;
  else if (patternError && ac0TrigTxListProc && trigDead_p)
    txAC0UPatternErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a pattern Error is detected on AC1 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC1UPatternErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC1UPatternErr <= 1'b0;
  else if (patternError && ac1TrigTxListProc && trigDead_p)
    txAC1UPatternErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a pattern Error is detected on AC2 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC2UPatternErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC2UPatternErr <= 1'b0;
  else if (patternError && ac2TrigTxListProc && trigDead_p)
    txAC2UPatternErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a pattern Error is detected on AC3 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC3UPatternErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC3UPatternErr <= 1'b0;
  else if (patternError && ac3TrigTxListProc && trigDead_p)
    txAC3UPatternErr <= 1'b1;
end


// // Indication to the DMA Status2 Register when a bus Error is detected
// // during a transmission
// assign txBcnBusErr = dmaHIFError && bcnTrigTxListProc;
// assign txAC0BusErr = dmaHIFError && ac0TrigTxListProc;
// assign txAC1BusErr = dmaHIFError && ac1TrigTxListProc;
// assign txAC2BusErr = dmaHIFError && ac2TrigTxListProc;
// assign txAC3BusErr = dmaHIFError && ac3TrigTxListProc;
// Indication to the DMA Status2 Register when a bus Error is detected
// during a transmission on BCN Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txBcnBusErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txBcnBusErr <= 1'b0;
  else if (dmaHIFError && bcnTrigTxListProc && trigDead_p)
    txBcnBusErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a bus Error is detected
// during a transmission on AC0 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC0BusErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC0BusErr <= 1'b0;
  else if (dmaHIFError && ac0TrigTxListProc && trigDead_p)
    txAC0BusErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a bus Error is detected
// during a transmission on AC1 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC1BusErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC1BusErr <= 1'b0;
  else if (dmaHIFError && ac1TrigTxListProc && trigDead_p)
    txAC1BusErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a bus Error is detected
// during a transmission on AC2 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC2BusErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC2BusErr <= 1'b0;
  else if (dmaHIFError && ac2TrigTxListProc && trigDead_p)
    txAC2BusErr <= 1'b1;
end

// Indication to the DMA Status2 Register when a bus Error is detected
// during a transmission on AC3 Channel
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC3BusErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC3BusErr <= 1'b0;
  else if (dmaHIFError && ac3TrigTxListProc && trigDead_p)
    txAC3BusErr <= 1'b1;
end

// // Indicates that the Transmit DMA channel did not find a valid PT address 
// // when reading the Header Descriptor.
// assign txBcnPTAddressErr = !plyTblValid && bcnTrigTxListProc;
// assign txAC0PTAddressErr = !plyTblValid && ac0TrigTxListProc;
// assign txAC1PTAddressErr = !plyTblValid && ac1TrigTxListProc;
// assign txAC2PTAddressErr = !plyTblValid && ac2TrigTxListProc;
// assign txAC3PTAddressErr = !plyTblValid && ac3TrigTxListProc;

// Indicates that the Transmit DMA channel did not find a valid PT address 
// when reading the Header Descriptor on BCN Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txBcnPTAddressErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txBcnPTAddressErr <= 1'b0;
  else if (!plyTblValid && bcnTrigTxListProc && trigDead_p)
    txBcnPTAddressErr <= 1'b1;
end

// Indicates that the Transmit DMA channel did not find a valid PT address 
// when reading the Header Descriptor on AC0 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC0PTAddressErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC0PTAddressErr <= 1'b0;
  else if (!plyTblValid && ac0TrigTxListProc && trigDead_p)
    txAC0PTAddressErr <= 1'b1;
end

// Indicates that the Transmit DMA channel did not find a valid PT address 
// when reading the Header Descriptor on AC1 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC1PTAddressErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC1PTAddressErr <= 1'b0;
  else if (!plyTblValid && ac1TrigTxListProc && trigDead_p)
    txAC1PTAddressErr <= 1'b1;
end

// Indicates that the Transmit DMA channel did not find a valid PT address 
// when reading the Header Descriptor on AC2 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC2PTAddressErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC2PTAddressErr <= 1'b0;
  else if (!plyTblValid && ac2TrigTxListProc && trigDead_p)
    txAC2PTAddressErr <= 1'b1;
end

// Indicates that the Transmit DMA channel did not find a valid PT address 
// when reading the Header Descriptor on AC3 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC3PTAddressErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC3PTAddressErr <= 1'b0;
  else if (!plyTblValid && ac3TrigTxListProc && trigDead_p)
    txAC3PTAddressErr <= 1'b1;
end

// // Indicates that the Transmit DMA channel found an invalid Next 
// // Atomic Frame Exchange Sequence Pointer or Next MPDU Descriptor Pointer.
// assign txBcnNextPointerErr = (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && bcnTrigTxListProc;
// assign txAC0NextPointerErr = (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac0TrigTxListProc;
// assign txAC1NextPointerErr = (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac1TrigTxListProc;
// assign txAC2NextPointerErr = (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac2TrigTxListProc;
// assign txAC3NextPointerErr = (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac3TrigTxListProc;

// Indicates that the Transmit DMA channel found an invalid Next 
// Atomic Frame Exchange Sequence Pointer or Next MPDU Descriptor Pointer
// on AC3 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txBcnNextPointerErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txBcnNextPointerErr <= 1'b0;
  else if ((!patternError) && (!dmaHIFError) && (plyTblValid) && (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && bcnTrigTxListProc && trigDead_p)
    txBcnNextPointerErr <= 1'b1;
end

// Indicates that the Transmit DMA channel found an invalid Next 
// Atomic Frame Exchange Sequence Pointer or Next MPDU Descriptor Pointer
// on AC0 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC0NextPointerErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC0NextPointerErr <= 1'b0;
  else if ((!patternError) && (!dmaHIFError) && (plyTblValid) && (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac0TrigTxListProc && trigDead_p)
    txAC0NextPointerErr <= 1'b1;
end

// Indicates that the Transmit DMA channel found an invalid Next 
// Atomic Frame Exchange Sequence Pointer or Next MPDU Descriptor Pointer
// on AC1 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC1NextPointerErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC1NextPointerErr <= 1'b0;
  else if ((!patternError) && (!dmaHIFError) && (plyTblValid) && (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac1TrigTxListProc && trigDead_p)
    txAC1NextPointerErr <= 1'b1;
end

// Indicates that the Transmit DMA channel found an invalid Next 
// Atomic Frame Exchange Sequence Pointer or Next MPDU Descriptor Pointer
// on AC2 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC2NextPointerErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC2NextPointerErr <= 1'b0;
  else if ((!patternError) && (!dmaHIFError) && (plyTblValid) && (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac2TrigTxListProc && trigDead_p)
    txAC2NextPointerErr <= 1'b1;
end

// Indicates that the Transmit DMA channel found an invalid Next 
// Atomic Frame Exchange Sequence Pointer or Next MPDU Descriptor Pointer
// on AC3 Channel.
always @(posedge macPITxClk or negedge macPITxClkHardRst_n)
begin
  if (macPITxClkHardRst_n == 1'b0)
    txAC3NextPointerErr <= 1'b0;
  else if (macPITxClkSoftRst_n == 1'b0)
    txAC3NextPointerErr <= 1'b0;
  else if ((!patternError) && (!dmaHIFError) && (plyTblValid) && (!nxtAtomFrmPtrValid || !nxtMpduDescValid) && ac3TrigTxListProc && trigDead_p)
    txAC3NextPointerErr <= 1'b1;
end

endmodule
