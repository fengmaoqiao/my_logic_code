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
// Description      : This module outputs the control signals to RAM
//                    The control signals are determined depending
//                    on the accessArbiter SM.
//                    memoryController SM has three states
//                    a) IDLE
//                    b) WRITE
//                    c) READ
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

module memoryController(
                        //$port_g Clock
                        input wire                    macCoreClk,        // System Clock
                        //$port_g Reset
                        input wire                    macCoreClkHardRst_n,// Hard Asynchrounous Reset
                        input wire                    macCoreClkSoftRst_n,         // Soft Synchronous Reset
                        //$port_g Inputs from accessArbiter
                        input wire                    hwUpdate,          // Flag set to one when HW
                                                                         // update is in progress
                        input wire                    ramWrEn,           // Trigger signal for RAM write
                                                                         // from accessArbiter
                        input wire                    ramRdEn,           // Trigger signal for RAM read
                                                                         // from accessArbiter
                        input wire                    mibTableResetTable,     // Indicates MIB Table reset
                        
                        //$port_g Output to accessArbiter
                        output reg                    ramUpdated,        // Indication for completion
                                                                         // of RAM update process
                                                                         // which can be either read
                                                                         // or write
                        
                        //$port_g Output to RAM
                        output reg                    mibTableWriteEn,        // Write enable signal to RAM
                        output reg                    mibRamRdEn,        // Read Enable signal to RAM
                        output reg                    mibTableEn           // Chip Select signal to RAM
                                                
                        );


   //***************INTERNAL REGISTERS****************//
   reg                               nextRamUpdated;
   reg                               nextCS;
   reg                               nextMibRamRdEn;
   reg                               nextmibTableWriteEn;
   
                 
   // Memory Controller has below given functions
   // a) Drives the data and control signals to RAM
   //    performing read/write operation
   // b) Latches the data received from RAM for read
   //    operation initiated.
   // c) indicates the rest of the sub block of
   //    mib controller that updated to ram is over
   // d) during HW update, memory controller reads
   //    desired location first and then adds the
   //    increment count to read data and writes
   //    back the updated value to same RAM location


   // Memory Controller is implemented as Mealy State
   // Machine.

   // memoryController FSM states definition
   //$fsm_sd memoryControllerCs
   localparam
             IDLE   =  2'd0,  // Default State
             READ   =  2'd1,  // Drives read control signal to ram
             WRITE  =  2'd2,  // Drives write control signal to ram
             UPDATE =  2'd3;  // Drives write control signal to ram
   
   // memoryController FSM signals definition
   reg [1:0]                         memoryControllerCs;  // memoryController FSM Current State
   reg [1:0]                         memoryControllerNs;  // memoryController FSM Next State
   
   
   
`ifdef RW_SIMU_ON
   // String definition to dislpay memoryController current state
   reg [6*8-1:0]                       memoryControllerCs_str;
`endif // RW_SIMU_ON
   
   
`ifdef RW_SIMU_ON
   // memoryController FSM states displayed in a string to easy simulation and debug
   always @*
begin
   case (memoryControllerCs)
        IDLE  :  memoryControllerCs_str = {"IDLE"};
        READ  :  memoryControllerCs_str = {"READ"};
       WRITE  :  memoryControllerCs_str = {"WRITE"};
      UPDATE  :  memoryControllerCs_str = {"UPDATE"};
     default  :  memoryControllerCs_str = {"XXX"};
   endcase
end
`endif // RW_SIMU_ON
   

   // memoryController SM is implemented as Mealy Machine.
   // Trigger Inputs   : Trigger signals from accessArbiter
   // Outputs          : a) Control Signals to RAM
   //                    b) Data and Address to RAM
   //
   // Attributes of SM : a) Mealy Machine
   //                    b) Three Always block implementation
   //                       1. For calculating next state and output (Combi Always block)
   //                       2. FF to get current State.
   //                       3. FF to register the outputs
   // accessArbiter FSM Current State Logic

   // 1 Always Block for obtaining current state.
   // Has two reset condition
   // a) Asynchronous reset - Power On Reset
   // b) Synchronous reset  - Software Trigger Reset.
   // Both this reset brings SM to state IDLE which
   // hence considered to be default state
   
   // memoryController FSM Current State Logic 
   always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
     begin
        if (macCoreClkHardRst_n == 1'b0)                          // Asynchronous Reset
          memoryControllerCs <= IDLE; 
        else if (macCoreClkSoftRst_n == 1'b0)                          // Synchronous Reset
          memoryControllerCs <= IDLE; 
        else
          memoryControllerCs <= memoryControllerNs; 
     end
   
   

   // Second always block is used to calculate
   // next state and output corresponding to that
   // state.
   // Next State is obtained according to control
   // signals obtained from accessArbiter.
   always @*
     begin

        // Clearing combi output
        // in order to avoid latch
        // inference
        nextRamUpdated      = 1'b0;
        nextCS              = 1'b0;
        nextMibRamRdEn      = 1'b0;
        nextmibTableWriteEn = 1'b0;
        
        case(memoryControllerCs)
          
          IDLE :
            //$fsm_s Default State
            begin

               // Condition : mibTableResetTable or ramWrEn
               // Source    : mibTableResetTable - accessArbiter
               //             ramWrEn       - accessArbiter
               // Set       : mibTableResetTable - This signal shall
               //                             set to one when
               //                             mib table reset bit
               //                             of macCntrlReg1 is set
               //                             which indicates that 0s
               //                             needs to be written to
               //                             every memory locations
               //                             in RAM.
               //             ramWrEn       - accessArbiter sets this 
               //                             bit to one when SW initiated
               //                             write operation is to be made.
               // Result    : in above two condition, memoryController needs
               //             to write at the designated RAM address.
               //             For mibTableResetTable data will be 0s
               //             For ramWrEn data shall be provided by
               //             host slave
               //$fsm_t In case of mibTableReset or ramWrEn,
               //memoryController SM shall move from IDLE
               //to WRITE state
               if(mibTableResetTable || ramWrEn)
                 begin
                    memoryControllerNs  = WRITE;
                    nextRamUpdated      = 1'b1;
                    nextCS              = 1'b1;
                    nextmibTableWriteEn = 1'b1;
                 end

               // Condition : ramRdEn or hwUpdate
               // Source    : ramRdEn  - accessArbiter
               //             hwUpdate - accessArbiter
               // Set       : ramRdEn  - accessArbiter sets
               //                        this flag when SW
               //                        read has to be made
               //                        to RAM location
               //                        indicated by address
               //                        provided by SW
               //             hwUpdate - when HW update is to be
               //                        made, update is done on the
               //                        existing value in RAM, hence
               //                        for that first RAM location
               //                        needs to be read first and then
               //                        updated
               // Result    : SM shall transit to READ, where it shall the
               //             read RAM location indicated by either address
               //             provided by SW in case of SW operation or
               //             address provided by dataLatch in case when
               //             HW update is to be made.
               else if(ramRdEn)
                 begin
                   //$fsm_t When ramRdEn or hwUpdate is ther
                   //memoryController SM shall move from IDLE
                   //to READ where RAM location indicated by
                   //address shall be read
                    memoryControllerNs = READ;
                    nextRamUpdated     = 1'b0;
                    nextCS             = 1'b1;
                    nextMibRamRdEn     = 1'b1;
                 end
               else if(hwUpdate)
                 begin
                    memoryControllerNs = READ;
                    nextCS             = 1'b1;
                    nextMibRamRdEn     = 1'b1;
                 end
               else
                 begin
                   //$fsm_t in absence of SW read or write or HW update
                   //or mibTableReset, SM shall remain in IDLE state
                    memoryControllerNs  = IDLE;
                    nextRamUpdated      = 1'b0;
                    nextCS              = 1'b0;
                    nextMibRamRdEn      = 1'b0;
                    nextmibTableWriteEn = 1'b0;
                 end
            end // case: IDLE
          
          READ :
            //$fsm_s When Read is to be made either
            // for 
            // a) HW Update of current RAM data and 
            // b) when SW read is initiated
            begin

               // Condition : hwUpdate
               // Source    : accessArbiter
               // Set       : Set by accessArbiter
               //             when HW update needs to
               //             made.
               // Result    : actve high in this signal
               //             shall indicate that hw update
               //             is in process and data read at
               //             previous read cycle needs to be
               //             updated by new value which will
               //             be equal to value read plus increment
               //             count obtained from dataLatch for this
               //             particular MIB
               if(hwUpdate)
                 begin
                     //$fsm_t If READ state is due to HW update, then
                     //Next state shall be UPDATE so as Write the updated
                     //value to the RAM
                    memoryControllerNs  = UPDATE;
                    nextCS              = 1'b0;
                    nextmibTableWriteEn = 1'b0;
                    nextRamUpdated      = 1'b0;
                 end
               else 
                 begin
                     //$fsm_t If READ is not HW update, then SM
                     //After driving control signals to RAM shall
                     //transit back to IDLE state
                    memoryControllerNs = IDLE;
                    nextRamUpdated      = 1'b1;
                    nextCS              = 1'b0;
                 end
            end // case: READ
          
          WRITE :
            //$fsm_s When Write is to be made either
            // for 
            // a) HW Update to current RAM data and 
            // b) when SW Write is initiated
            begin

               // Condition : mibTableResetTable
               // Source    : accessArbiter
               // Set       : this flag is set
               //             when MIB table needs
               //             reset by writting 0s
               //             to every RAM locations
               // Result    : ramUpdated for previous state
               //             shall ensure that update to
               //             previous RAM location is done
               //             and now address present shall
               //             be of next RAM location where 0s
               //             needs to be written
               //
               if(mibTableResetTable)
                 begin
                     //$fsm_t In case of mibTableResetTable, continues write of 00
                     //has to be made to every consecutive RAM location, hence
                     //after every write SM enters again to WRITE state for
                     //next write
                    memoryControllerNs  = WRITE;
                    nextRamUpdated      = 1'b1;
                    nextmibTableWriteEn = 1'b1;
                    nextCS              = 1'b1;
                 end

               // Condition : hwUpdate
               // Source    : accessArbiter
               // Set       : set when HW update for
               //             active MIB is in progress
               // Result    : if set to one, then update
               //             previous RAM location is
               //             done and now address is available
               //             for next RAM location which needs
               //             to be read first and then update
               //             should be done
               else if (hwUpdate)
                 begin
                     //$fsm_t In case of HWUpdate then, SM shall move
                     //from WRITE state to READ for getting next MIB
                     //value from RAM which gets updated next
                    memoryControllerNs = READ;
                    nextMibRamRdEn     = 1'b1;
                    nextCS             = 1'b1;
                 end
               else
                 begin
                    //$fsm_t If the READ was initiated due as SW process
                    //then after READ SM moves to IDLE state
                    memoryControllerNs = IDLE;
                 end
            end // case: WRITE

          UPDATE :
            //$fsm_s When Read Mod Write is required, the FSM stays in UPDATE 
            // for one clock cycle. That allows to capture the read data before modifying it

             //$fsm_t Moves to WRITE after one clock cycle
            begin
               nextMibRamRdEn      = 1'b0;
               nextCS              = 1'b1;
               nextmibTableWriteEn = 1'b1;
               nextRamUpdated      = 1'b1;
               memoryControllerNs  = WRITE;
            end

          default :
            begin
               nextmibTableWriteEn = 1'b0;
               nextRamUpdated      = 1'b0;
               nextCS              = 1'b0;
               nextMibRamRdEn      = 1'b0;
               memoryControllerNs  = IDLE;
            end
        endcase // case(memoryControllerCs)
     end // always@ (memoryControllerCs...
   

   
   // Registering Outputs
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          begin
             ramUpdated      <= 1'b0;
             mibTableEn      <= 1'b0;
             mibRamRdEn      <= 1'b0;
             mibTableWriteEn <= 1'b0;
          end
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             ramUpdated      <= 1'b0;
             mibTableEn      <= 1'b0;
             mibRamRdEn      <= 1'b0;
             mibTableWriteEn <= 1'b0;
          end
        else
          begin
             ramUpdated      <= nextRamUpdated;
             mibTableEn      <= nextCS;
             mibRamRdEn      <= nextMibRamRdEn;
             mibTableWriteEn <= nextmibTableWriteEn;
          
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n = 1'b0)

endmodule // memoryController
