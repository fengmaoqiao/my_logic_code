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
// Description      : Access Arbiter implements a State Machine which shall
//                    get trigger from either
//                    a) Host Inteterface so as to perform SW read or write
//                    b) dataLatch(mibTrigger from MAC Controller) so as to
//                    perform HW update of the active MIBs.
//
//                    State Machine implemented is Mealy State MAchine with
//                    three always block
//                    1. one for calculating next state
//                    2. second for registering the state
//                    3. third for registering the output of SM
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
module accessArbiter(
                     //$port_g  Clock and Reset
                     input wire                      macCoreClk,           // MAC Core Clock
                     input wire                      macCoreClkHardRst_n,  // Hard Reset Active Low
                     input wire                      macCoreClkSoftRst_n,  // Soft Reset Active Low
                     
                     //$port_g  Input from host
                     input wire [`RW_MIB_ADDR_WIDTH-1 : 0] mibAddr,        // Address From Host
                     input wire                            mibRd,
                     
                     //$port_g Input from register
                     input  wire [9 :0]              mibTableIndex,        // MIB Table Index in the MIB Table that needs to be updated.
                     input  wire                     mibIncrementMode,     // MIB Increment Mode
                                                                           //   When set, the contents of the MIB entry pointed to 
                                                                           //   by the mibTableIndex are incremented by the mibValue.
                                                                           //   When reset, the contents of the MIB entry pointed to 
                                                                           //   by the mibTableIndex are overwritten by the mibValue.
                     
                     input  wire [15:0]              mibValue,             // MIB Value
                     input  wire                     mibWrite,             // MIB Write
                     input wire                      mibTableReset,        // Indicates that mib 
                                                                           // table reset bit is 
                                                                           // set in macCntrlReg1
                     output wire                     mibWriteInValid,      // Clear the mibWrite bit
                     output wire                     mibWriteIn,           // mibWrite
                     output wire                     mibTableResetIn,      // mibTableResetIn  
                     output wire                     mibTableResetInValid, // Clear the mibTableReset bit

                     //$port_g Input from dataLatch
                     input wire                      mibHWUpdateStart,     // Indicates that MIB
                                                                           // update has started
                     input wire                      mibTrigger,           // Indicates that MIB
                                                                           // update has started
                     
                     //$port_g Input from MemoryController
                     input wire                      ramUpdated,           // Indication from
                                                                           // memeoryController for
                                                                           // end of RAM update. 
                     

                     //$port_g Input from RAM
                     input wire [`RW_MIB_DATA_WIDTH-1 :0] mibTableReadData,// Read Data from RAM
                     
                     //$port_g Output to MemoryController
                     output reg                      ramWrEn,              // Trigger to memoryController
                                                                           // to begin Write process to
                                                                           // RAM                    
                     output reg                      ramRdEn,              // Trigger to memoryController
                                                                           // to begin read process from
                                                                           // RAM
                     output reg                      hwUpdate,             // indicates that HW update 
                                                                           // for active MIB 
                                                                           // has been started. Trigger
                                                                           // for memoryController SM
                     output wire [`RW_MIB_ADDR_WIDTH-1 :0] mibTableArbAddr,// RAM Address during RESET
                                                                           // or SW Accesses
                     output reg  [`RW_MIB_DATA_WIDTH-1 :0] mibTableArbData,// RAM Write Data during RESET
                                                                           // or SW Accesses
                     //$port_g Output to host
                     output reg                      mibBusy,              // Indicates Host Slave
                                                                           // that MIB is busy in
                                                                           // updating the RAM for
                                                                           // SW operation initiated

                     //$port_g Output to dataLatch
                     output reg                      mibTableResetTable,   // Indicates table reset
                                                                           // is in progress
                     output reg                      clearEvent            // Indicates clearing of
                                                                           // MIB fields and tid Index
                                                                           // latched during mibTrigger
                     
                     );

   

   //**************Internal Register****************//
   reg    nextClrEvent;
   reg    nextRamWrEn;
   reg    nextRamRdEn;
   reg    nextMibBusy;
   reg    nextHWUpdate;
   reg    nextmibTableResetTable;
   
   reg [`RW_MIB_ADDR_WIDTH-1 :0] mibTableResetRamAddr; // RAM Address during RESET
                                                  // table
                                                  // memoryController 
   
   
   reg [`RW_MIB_ADDR_WIDTH-1 :0] mibAddrCapt;         // Address From Host
   reg                    mibRdCapt;
  
   reg                    mibWriteCapt;        // MIB Write
   //reg                    mibTableResetCapt;   // Indicates that mib 
                                               // table reset bit is 
                                               // set in macCntrlReg1
   reg                    mibTriggerCapt;
     
   /****************************************************/
   //      SM Generated Using FSM Generator Script     //
   /////////////////////////////////////////////////////
   // accessArbiter FSM states definition
   //$fsm_sd accessArbiterCs
   localparam
             RESETTABLE  =  3'd0,  // MIB table needs to be reset with 0s 
             IDLE        =  3'd1,  // Default state
             SWREAD      =  3'd2,  // SW read operation performed
             SWWRITE     =  3'd3,  // SW write operation performed
             MIBUPDATE   =  3'd4,  // HW Update of active MIB
             SWINCREMENT =  3'd5;  // SW increment operation performed
   
   
   localparam ALLONE_CT = 32'hffffffff;
   
   // accessArbiter FSM signals definition
   reg [2:0] accessArbiterCs;  // accessArbiter FSM Current State
   reg [2:0] accessArbiterNs;  // accessArbiter FSM Next State

   wire [`RW_MIB_ADDR_WIDTH-1 :0]  mibLastAddr;
   
`ifdef RW_SIMU_ON
   // String definition to dislpay accessArbiter current state
   reg [11*8:0] accessArbiterCs_str;
`endif // RW_SIMU_ON
   
   

   assign mibLastAddr =  {ALLONE_CT[`RW_MIB_ADDR_WIDTH-3:0],2'b11};

   // accessArbiter SM is implemented as Mealy Machine.
   // Trigger Inputs   : a) dataLatch Sub Module
   //                    b) Host Slave
   // Outputs          : a) Triggers memory Controller
   //                       SM
   //                    b) clearEvent output clears
   //                       MIB and TID index latched
   //                       during mibTrigger
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
   
   always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
     begin
        if (macCoreClkHardRst_n == 1'b0)                  // Asynchronous Reset
          accessArbiterCs <= IDLE; 
        else if (macCoreClkSoftRst_n == 1'b0)          // Synchronous Reset
          accessArbiterCs <= IDLE; 
        else
          accessArbiterCs <= accessArbiterNs; 
     end
   
   /////////////////////////////////////////////////////
   ///////////////////SM Define Over////////////////////

   
   // Second Always Block for obtaining next state
   // and outputs.
   // Next State is calculated based on inputs
   // from a) Host Slave Interface so as to perform
   //         SW operation of either Read or Write
   //      b) dataLatch Module which shall trigger
   //         HW update of the RAM
   //      c) Also gets inputs from MAC which
   //         shall indicate reset of MIB table
   //         in RAM
   always @*
     begin
        
        // Clearing all output register so as to
        // avoid inferring latch by SM
        nextmibTableResetTable = 1'b0;
        nextClrEvent      = 1'b0;
        nextRamRdEn       = 1'b0;
        nextMibBusy       = 1'b0;
        nextRamWrEn       = 1'b0;
        nextHWUpdate      = 1'b0;
        case(accessArbiterCs)
          
          RESETTABLE:
          //$fsm_s RESET State where MIB Resets whole
          // MIB Table. It gets trigger by setting
          // mib reset table bit in macCntrlReg1.
            begin
               // Condition : mibHWUpdateStart
               // Source    : dataLatch module
               // Set       : Set when all active MIBs
               //             which were suppose to get
               //             update ar over.
               // Result    : SM Transits back to IDLE
               //             as there are no Active MIB
               //             which needs to get updated in
               //             RAM
               //$fsm_t While clearing every RAM location
               //during Reset Table indications, if Address
               //reached is last MIB address then in that case
               //RESETTABLE should exit to IDLE state
//                if((mibTableResetRamAddr == `ACTIVE_MIB_LAST_ADDR))
               if((mibTableResetRamAddr == mibLastAddr))
                 begin
                    accessArbiterNs = IDLE;
                    nextmibTableResetTable = 1'b0;
                 end

               // Else Maintain the current state
               // where update is made to RAM for
               // respective active MIB address
               // obtained from dataLatch
               //$fsm_t till mibHWUpdateStart is not set
               //SM shall remian in RESETTABLE state
               else
                 begin
                    nextmibTableResetTable = 1'b1;
                    accessArbiterNs   = RESETTABLE;
               end
            end // case: accessArbiterCs[B_RESETTABLE]
          
          IDLE:
          //$fsm_s Default State.
            begin

               // Condition : mibTableReset
               // Source    : MAC
               // Set       : shall get set when MIB Table
               //             reset bit is set to one in
               //             macCntrl1Reg
               // Result    : mibTableReset is triggered where
               //             zeros are written at every
               //             locaton in RAM.
               //             During mibTableReset, HW update
               //             needs to be cleared if any.
               //$fsm_t on indication for mibTableReset from
               //Host Slave, SM shall transit from IDLE
               //to RESETTABLE state and it shall set
               //ClearEvent and mibTableResetTable bit high
               //if((mibTableReset || mibTableResetCapt) && !mibTriggerCapt)
               if(mibTableReset  && !mibTriggerCapt)
                 begin
                    accessArbiterNs   = RESETTABLE;
                    nextClrEvent      = 1'b1;
                    nextmibTableResetTable = 1'b1;
                 end

               // Condition : mibRd
               // Source    : Host Slave
               // Set       : when software read needs to
               //             be made.
               // Result    : SW Read Process is initiated
               //             by transitting to SWRead State
               //             which triggers the memory Controller
               //             SM for readig the RAM location indicated by
               //             address.
               // 
               //$fsm_t on indication for mibRd from
               //Host Slave, SM shall transit from IDLE
               //to SWREAD state and it shall set
               //nextRamRdEn bit high
               else if((mibRd || mibRdCapt) && !mibTriggerCapt)
                 begin
                    // Next State 
                    accessArbiterNs = SWREAD;
                    // Output at next State
                    nextClrEvent    = 1'b1;
                    nextRamRdEn     = 1'b1;
                    nextMibBusy     = 1'b1;
                 end

               //       Condition : mibWrite and not mibIncrementMode
               //       Source    : Registers
               //       Set       : when software write needs to
               //                   be made.
               //       Result    : SW Write Process is initiated
               //                   by transitting to SWWrite State
               //                   which triggers the memory Controller
               //                   SM for writing data obtained from
               //                   register to RAM location indicated by
               //                   address.
               //$fsm_t on indication for mibRd from
               //Host Slave, SM shall transit from IDLE
               //to SWWRITE state and it shall set
               //nextRamWrEn bit high
               else if((mibWrite || mibWriteCapt) && !mibIncrementMode && !mibTriggerCapt)
                 begin
                    // Next State
                    accessArbiterNs = SWWRITE;
                    // Output at next State
                    nextClrEvent    = 1'b1;
                    nextRamWrEn     = 1'b1;
                    nextMibBusy     = 1'b1;
                 end

               //       Condition : mibWrite and mibIncrementMode
               //       Source    : Register
               //       Set       : when software incremental write needs to
               //                   be made.
               //       Result    : SW Increment Process is initiated
               //                   by transitting to SWINCREMENT State
               //                   which triggers the memory Controller
               //                   SM for reading the index mibTableIndex,
               //                   increment the read value and write it 
               //                   back to the RAM
               //$fsm_t on indication for mibRd from
               //Host Slave, SM shall transit from IDLE
               //to SWINCREMENT state and it shall set
               //nextRamRdEn bit high
               else if((mibWrite || mibWriteCapt) && mibIncrementMode && !mibTriggerCapt)
                 begin
                    // Next State
                    accessArbiterNs = SWINCREMENT;
                    // Output at next State
                    nextClrEvent    = 1'b1;
                    nextRamRdEn     = 1'b1;
                    nextMibBusy     = 1'b1;
                 end

               //        Condition : mibTrigger and mibHWUpdateStart
               //        Source    : Host Slave
               //        Set       : when HW update is to be made.
               //        Result    : With latching of the MIB Fields
               //                    by mibTrigger, accessArbiter SM
               //                   is trigger for HW update.
               //$fsm_t When  mibHWUpdateStart is there 
               // shall indicate accessArbiter SM of HWUpdate
               // has began and dataLatch is ready with RAM address 
               // of active MIB which needs to be updated
               //HWUpdate state from IDLE state
               else if(mibHWUpdateStart)
                 begin
                    // Next State
                    accessArbiterNs = MIBUPDATE;
                    // Output at next State
                    nextHWUpdate    = 1'b1;
                 end

               // Condition : Failing to do above, SM
               //             shall maintain the default
               //             state.
               //$fsm_t In IDLE state if there are no
               //SW request and no HW update then SM
               //shall remain in IDLE state
               else
                 begin
                    accessArbiterNs   = IDLE;
                    // Clearing every Output
                    nextClrEvent      = 1'b0;
                    nextRamRdEn       = 1'b0;
                    nextHWUpdate      = 1'b0;
                    nextRamWrEn       = 1'b0;
                    nextMibBusy       = 1'b0;
                    nextmibTableResetTable = 1'b0;
                 end
            end // case: accessArbiterCs[B_IDLE]
          
          SWREAD:
          //$fsm_s SWRead State which initiates the
          // SW read of the RAM location indicated
          // by address provided by Host.
            begin

               // Condition : ramUpdated
               // Source    : memoryController
               // Set       : ramUpdated bit is set
               //             to indicate the completion
               //             RAM related operation which
               //             which can be either writting
               //             to RAM or reading from RAM
               // Result    : ramUpdated shall indicate that
               //             RAM has beed read for the address
               //             passed, hence transit back to
               //             IDLE state
               //$fsm_t With indication for ramUpdated, SM shall
               //shall move from SWREAD to IDLE with finish of
               //SW read process
               if(ramUpdated)
                 begin
                    // Next State
                    accessArbiterNs = IDLE;
                    // Output at next state
                    nextMibBusy     = 1'b0;
                 end

               // Condition : RAM is not yet updated.
               // Result    : maintain current state
               //             till indication is obtained
               //             for RAM is read
               //$fsm_t Till ramUpdated indication is received
               //SM shall remain in SWREAD state indicating
               //SW read is still in process
               else
                 begin
                    accessArbiterNs = SWREAD;
                    nextMibBusy     = 1'b1;
                 end
            end // case: accessArbiterCs[B_SWREAD]

          SWWRITE:
          //$fsm_s SWWrite State which initiates the
          // SW write to RAM location with data
          // and address provided by Host   
            begin

               // Condition : ramUpdated
               // Source    : memoryController
               // Set       : ramUpdated bit is set
               //             to indicate the completion
               //             RAM related operation 
               //             which can be either writting
               //             to RAM or reading from RAM
               // Result    : ramUpdated shall indicate that
               //             RAM has written data obtained to
               //             the RAM, hence transit back to
               //             IDLE state
               //$fsm_t With indication for ramUpdated, SM shall
               //shall move from SWWRITE to IDLE with finish of
               //SW write process to RAM
               if(ramUpdated)
                 begin
                    // Next State 
                    accessArbiterNs = IDLE;

                    // Output at next State
                    nextMibBusy     = 1'b0;
                 end

               // Condition : RAM is not yet updated.
               // Result    : maintain current state
               //             till indication is obtained
               //             for RAM write is complete
               
               //$fsm_t Till ramUpdated indication is received
               //SM shall remain in SWREAD state indicating
               //SW read is still in process
               else
                 begin
                    accessArbiterNs = SWWRITE;
                    nextMibBusy     = 1'b1;
                 end
            end // case: accessArbiterCs[B_SWWRITE]

          SWINCREMENT:
          //$fsm_s SWIncrement State which initiates the
          // SW read from RAM location at address provided 
          // by register. 
            begin

               // Condition : ramUpdated
               // Source    : memoryController
               // Set       : ramUpdated bit is set
               //             to indicate the completion
               //             RAM related operation 
               //             which can be either writting
               //             to RAM or reading from RAM
               // Result    : ramUpdated shall indicate that
               //             RAM has read data, hence transit to
               //             SWWRITE state
               //$fsm_t With indication for ramUpdated, SM shall
               //move from SWINCREMENT to SWWRITE with finish of
               //SW read process to RAM
               if(ramUpdated)
                 begin
                    // Next State 
                    accessArbiterNs = SWWRITE;
                    nextRamWrEn     = 1'b1;

                    // Output at next State
                    nextMibBusy     = 1'b1;
                 end

               // Condition : RAM is not yet updated.
               // Result    : maintain current state
               //             till indication is obtained
               //             for RAM write is complete
               
               //$fsm_t Till ramUpdated indication is received
               //SM shall remain in SWREAD state indicating
               //SW read is still in process
               else
                 begin
                    accessArbiterNs = SWINCREMENT;
                    nextMibBusy     = 1'b1;
                 end
            end // case: accessArbiterCs[B_SWWRITE]

          MIBUPDATE:
          //$fsm_s MIBUPDATE State where update of active MIB
          //is performed, active MIB which are latched
          //during MIB Trigger from MAC Controller
            begin
               //$fsm_t If RAM is updated and no HW update
               // then goes back to IDLE
               if(!mibHWUpdateStart && ramUpdated)
                 begin
                    // Next State
                    accessArbiterNs = IDLE;
                    nextHWUpdate    = 1'b0;
                    nextClrEvent    = 1'b0;
                 end

               //$fsm_t Else Maintain the HW Update state
               // continue Forwarding next active
               // MIB address which needs to be
               // updated
               // 
               else
                 begin
                    nextHWUpdate    = 1'b1;
                    accessArbiterNs = MIBUPDATE;
                 end
            end // accessArbiterCs[B_MIBUPDATE]
          default: accessArbiterNs = IDLE;
        endcase // case(1'b1)
     end // always@ (accessArbiterCs...
   

   // Force the mibWriteIn to zero to clear the mibWrite register
   assign mibWriteIn = 1'b0;

   // Indicates the completion of the mibWrite register
   assign mibWriteInValid = ((accessArbiterCs == SWWRITE) && (accessArbiterNs == IDLE)) ? 1'b1 : 1'b0;

   // Force the mibTableResetIn to zero to clear the mibTableReset register
   assign mibTableResetIn = 1'b0;

   // Indicates the completion of the mibTableReset register
   assign mibTableResetInValid = ((accessArbiterCs == RESETTABLE) && (accessArbiterNs == IDLE)) ? 1'b1 : 1'b0;


   // Registering outputs
   always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin

        // Source : Power On Reset Asynchronous Reset
        // Result : Resets every flop asynchrounously
        if(macCoreClkHardRst_n == 1'b0)                                     
          begin
             clearEvent    <= 1'b0;
             hwUpdate      <= 1'b0;
             ramRdEn       <= 1'b0;
             ramWrEn       <= 1'b0;
             mibBusy       <= 1'b0;
             mibTableResetTable <= 1'b0;
          end

        // Source : Software reset Synchrounous Reset
        // Result : Resets every flop synchrounously
        else if (macCoreClkSoftRst_n == 1'b0)
          begin
             clearEvent    <= 1'b0;
             hwUpdate      <= 1'b0;
             ramRdEn       <= 1'b0;
             ramWrEn       <= 1'b0;
             mibBusy       <= 1'b0;
             mibTableResetTable <= 1'b0;
          end

        else
          begin
             clearEvent    <= nextClrEvent;
             hwUpdate      <= nextHWUpdate;
             ramRdEn       <= nextRamRdEn;
             ramWrEn       <= nextRamWrEn;
             mibBusy       <= nextMibBusy;
             mibTableResetTable <= nextmibTableResetTable;
          end // else: !if(macCoreClkHardRst_n)
     end // always@ (posedge macCoreClk or negedge rst_n = 1'b0)
   

   
   
   // Below logic shall generate the RAM addresses when MIB reset is
   // initiated. During MIB reset, consecutive RAM address shall
   // be generated till last RAM address is updated. Last
   // MIB address shall be indicated by `ACTIVE_MIB_LAST_ADDR
   always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibTableResetRamAddr    <= `RW_MIB_ADDR_WIDTH'd0;
          end
        else if (macCoreClkSoftRst_n == 1'b0)
          begin
             mibTableResetRamAddr    <= `RW_MIB_ADDR_WIDTH'd0;
          end
        else if( (accessArbiterCs != RESETTABLE) && (accessArbiterNs == RESETTABLE))
            begin
               mibTableResetRamAddr  <= `RW_MIB_ADDR_WIDTH'd0;
            end
//         else if(mibTableResetTable && ramUpdated && (mibTableResetRamAddr != `ACTIVE_MIB_LAST_ADDR))
        else if(mibTableResetTable && ramUpdated && (mibTableResetRamAddr != mibLastAddr))
          begin
             mibTableResetRamAddr    <= mibTableResetRamAddr + `RW_MIB_ADDR_WIDTH'd1;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)
   
  // In RESETTABLE state, the RAM Address comes from mibTableResetRamAddr
  // In SWREAD state, the RAM Address comes from the Host (mibAddr)
  // Else, the RAM Address comes from the register (mibTableIndex)
  assign mibTableArbAddr = (accessArbiterCs == RESETTABLE) ? mibTableResetRamAddr : (accessArbiterCs == SWREAD) ? mibAddrCapt : mibTableIndex[`RW_MIB_ADDR_WIDTH-1 :0];
   
  // In RESETTABLE state, the RAM is written with 0.
  // In case of mibIncrementMode, the RAM is written with the read data plus the increment (mibValue).
  // Else, the RAM is writen with mibValue
//  assign mibTableArbData = (accessArbiterCs == SWWRITE) ?  (mibIncrementMode) ? mibTableReadData + {16'b0,mibValue} : {16'b0,mibValue} : 0;
  always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
  begin
    if (macCoreClkHardRst_n == 1'b0)
       mibTableArbData    <= `RW_MIB_DATA_WIDTH'd0;
    else if (macCoreClkSoftRst_n == 1'b0)
       mibTableArbData    <= `RW_MIB_DATA_WIDTH'd0;
    else 
    begin
      if (accessArbiterCs == SWWRITE)
      begin
        if (mibIncrementMode)
          mibTableArbData <= mibTableReadData + {16'b0,mibValue};
        else  
          mibTableArbData <= {16'b0,mibValue};
      end
      else
        mibTableArbData <=  `RW_MIB_DATA_WIDTH'd0;
    end   
  end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)


  always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
  begin
    if (macCoreClkHardRst_n == 1'b0)
       mibAddrCapt    <= `RW_MIB_ADDR_WIDTH'd0;
    else if (macCoreClkSoftRst_n == 1'b0)
       mibAddrCapt    <= `RW_MIB_ADDR_WIDTH'd0;
    else 
    begin
      if (mibRd || mibWrite)
        mibAddrCapt <= mibAddr;
    end
  end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)

  always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
  begin
    if (macCoreClkHardRst_n == 1'b0)
       mibRdCapt    <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0)
       mibRdCapt    <= 1'b0;
    else 
    begin
      if (mibRd)
        mibRdCapt <= mibRd;
      else if (accessArbiterCs == SWREAD)
        mibRdCapt <= 1'b0;      
    end    
  end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)

  always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
  begin
    if (macCoreClkHardRst_n == 1'b0)
       mibWriteCapt    <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0)
       mibWriteCapt    <= 1'b0;
    else 
    begin
      if (mibWrite)
      begin
        if ((accessArbiterCs == SWWRITE) || (accessArbiterCs == SWINCREMENT))
          mibWriteCapt <= 1'b0;      
        else  
          mibWriteCapt <= 1'b1;
      end    
    end    
  end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)

  //always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
  //begin
  //  if (macCoreClkHardRst_n == 1'b0)
  //     mibTableResetCapt    <= 1'b0;
  //  else 
  //  begin
  //    if (mibTableReset)
  //      mibTableResetCapt <= mibTableReset;
  //    else if (accessArbiterCs == RESETTABLE)
  //      mibTableResetCapt <= 0;      
  //  end    
  //end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)

  always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
  begin
    if (macCoreClkHardRst_n == 1'b0)
      mibTriggerCapt    <= 1'b0;
    else if(macCoreClkSoftRst_n == 1'b1)
      mibTriggerCapt    <= 1'b0;
    else 
    begin
      if (mibTrigger)
        mibTriggerCapt <= mibTrigger;
      else if (accessArbiterCs == MIBUPDATE)
        mibTriggerCapt <= 1'b0;      
    end    
  end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)




///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////



`ifdef RW_SIMU_ON
// accessArbiter FSM states displayed in a string to easy simulation and debug
   always @*
     begin
        case (accessArbiterCs)
          RESETTABLE  :  accessArbiterCs_str = {"RESETTABLE"};
          IDLE        :  accessArbiterCs_str = {"IDLE"};
          SWREAD      :  accessArbiterCs_str = {"SWREAD"};
          SWWRITE     :  accessArbiterCs_str = {"SWWRITE"};
          MIBUPDATE   :  accessArbiterCs_str = {"MIBUPDATE"};
          SWINCREMENT :  accessArbiterCs_str = {"SWINCREMENT"};
          default     :  accessArbiterCs_str = {"XXX"};
   endcase
     end
`endif // RW_SIMU_ON

endmodule // accessArbiter




