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
// Description      : This is top file which interfaces
//                    with a) RAM
//                         b) HOST
//                         c) MAC Controller
//
//                    It incorporates the instantiation of the other
//                    sub modules like
//                    a) dataLatch        - It Latches the MIB Fields and generates the RAM address of
//                                          ACTIVE MIBS.
//                    b) accessArbiter    - It is SM from which decides which function needs
//                                          to be performed, like SW Read or Write or HW Update
//                    c) memoryController - It drives the control and data signals to RAM
//                    RAM Read/Write MUX  - MUX is implemented for address and data to be fowarded
//                                          to RAM.
//                                          MUX selects the address and data between:
//                                          a) Address/Data from dataLatch module for MIB Update
//                                          b) Address/Data from Host slave interface.
//                    
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
module mibController(
                  //$port_g  MIBs input from Top
                  input wire                          mibdot11WEPExcludedCount,                 // Count the number of unencrypted frames that have been discarded.                                                                                                                                    
                  input wire                          mibdot11FCSErrorCount,                    // Count the receive FCS errors.                                                                                                                                                                       
                  input wire                          mibrwRxPHYErrorCount,                     // Count the number of PHY Errors reported during a receive transaction.                                                                                                                               
                  input wire                          mibrwRxFIFOOverflowCount,                 // Count the number of times the Receive FIFO has overflowed.                                                                                                                                          
                  input wire                          mibrwTxUnderrunCount,                     // Count the number of times underrun has occurred on the Transmit side .                                                                                                                              
                  input wire                          mibrwQosUTransmittedMPDUCount,            // Count the number of unicast MPDUs, not containing an A-MSDU, that were transmitted successfully without using BA policy.                                                                            
                  input wire                          mibrwQosGTransmittedMPDUCount,            // Count the number of group-addressed MPDUs, not containing an A-MSDU, that were transmitted successfully.                                                                                            
                  input wire                          mibdot11QosFailedCount,                   // Count the number of MSDUs or MMPDUs that were discarded because of retry-limit-reached condition.                                                                                                   
                  input wire                          mibdot11QosRetryCount,                    // Count the number of unfragmented MSDUs or unfragmented MMPDUs that were transmitted successfully after 1 or more retransmissions without using BA policy.                                           
                  input wire                          mibdot11QosRTSSuccessCount,               // Count the number of successful RTS frame transmissions.                                                                                                                                             
                  input wire                          mibdot11QosRTSFailureCount,               // Count the number of unsuccessful RTS frame transmissions                                                                                                                                            
                  input wire                          mibrwQosACKFailureCount,                  // Count the number of MPDUs, not containing an A-MSDU, that did not receive an ACK frame successfully in response.                                                                                    
                  input wire                          mibrwQosUReceivedMPDUCount,               // Count the number of unicast MPDUs, not containing an A-MSDU, received successfully, destined to this device.                                                                                        
                  input wire                          mibrwQosGReceivedMPDUCount,               // Count the number of group-addressed MPDUs, not containing an A-MSDU, received successfully.                                                                                                         
                  input wire                          mibrwQosUReceivedOtherMPDU,               // Count the number of unicast MPDUs, not containing an A-MSDU, received successfully, not destined to this device.                                                                                    
                  input wire                          mibdot11QosRetriesReceivedCount,          // Count the number of MPDUs that are received with the retry bit set.                                                                                                                                 
                  input wire                          mibrwUTransmittedAMSDUCount,              // Count the number of unicast A-MSDUs that were transmitted successfully without using BA policy.                                                                                                     
                  input wire                          mibrwGTransmittedAMSDUCount,              // Count the number of group-addressed A-MSDUs that were transmitted successfully .                                                                                                                    
                  input wire                          mibdot11FailedAMSDUCount,                 // Count the number of A-MSDUs that were discarded because of retry-limit-reached condition.                                                                                                           
                  input wire                          mibdot11RetryAMSDUCount,                  // Count the number of A-MSDUs that were transmitted successfully after 1 or more retransmissions without using BA policy.                                                                             
                  input wire [15 : 0]                 mibdot11TransmittedOctetsInAMSDU,         // Count the number of bytes in the frame body of an A-MSDU that was transmitted successfully without using BA policy .                                                                                
                  input wire                          mibdot11AMSDUAckFailureCount,             // Count the number of A-MSDUs that did not receive an ACK frame successfully in response.                                                                                                             
                  input wire                          mibrwUReceivedAMSDUCount,                 // Count the number of unicast A-MSDUs received successfully, destined to this device.                                                                                                                 
                  input wire                          mibrwGReceivedAMSDUCount,                 // Count the number of group-addressed A-MSDUs received successfully.                                                                                                                                  
                  input wire                          mibrwUReceivedOtherAMSDU,                 // Count the number of unicast A-MSDUs received successfully, not destined to this device.                                                                                                             
                  input wire [15 : 0]                 mibdot11ReceivedOctetsInAMSDUCount,       // Count the number of bytes in the frame body of an A-MSDU that was received successfully.                                                                                                            
                  input wire                          mibdot11TransmittedAMPDUCount,            // Count the number of A-MPDUs that were transmitted.                                                                                                                                                  
                  input wire                          mibdot11TransmittedMPDUInAMPDUCount,      // Count the number of MPDUs that were transmitted in an A-MPDU.                                                                                                                                       
                  input wire [15 : 0]                 mibdot11TransmittedOctetsInAMPDUCount,    // Count the number of bytes in a transmitted A-MPDU.                                                                                                                                                  
                  input wire                          mibrwUAMPDUReceivedCount,                 // Count the number of unicast A-MPDUs received, destined to this device.                                                                                                                              
                  input wire                          mibrwGAMPDUReceivedCount,                 // Count the number of group-addressed A-MPDUs received.                                                                                                                                               
                  input wire                          mibrwOtherAMPDUReceivedCount,             // Count the number of unicast A-MPDUs received, not destined to this device.                                                                                                                          
                  input wire                          mibdot11MPDUInReceivedAMPDUCount,         // Count the number of MPDUs that were received in an A-MPDU.                                                                                                                                          
                  input wire [15 : 0]                 mibdot11ReceivedOctetsInAMPDUCount,       // Count the number of bytes received in an A-MPDU.                                                                                                                                                    
                  input wire [7 : 0]                  mibdot11AMPDUDelimiterCRCErrorCount,      // Count the number of CRC errors in MPDU Delimiter of an A-MPDU. An immediately repeated CRC error within an A-MPDU is not counted.                                                                   
                  input wire                          mibdot11ImplicitBARFailureCount,          // Count the number of Implicit BAR frames that did not receive the BA frame successfully in response.                                                                                                 
                  input wire                          mibdot11ExplicitBARFailureCount,          // Count the number of Explicit BAR frames that did not receive the BA frame successfully in response.                                                                                                 
                  input wire                          mibdot1120MHzFrameTransmittedCount,       // Count the number of frames transmitted at 20 MHz BW.                                                                                                                                                
                  input wire                          mibdot1140MHzFrameTransmittedCount,       // Count the number of frames transmitted at 40 MHz BW.                                                                                                                                                
                  input wire                          mibdot1180MHzFrameTransmittedCount,       // Count the number of frames transmitted at 80 MHz BW.                                                                                                                                                
                  input wire                          mibdot11160MHzFrameTransmittedCount,      // Count the number of frames transmitted at 160 MHz BW.                                                                                                                                               
                  input wire                          mibdot1120MHzFrameReceivedCount,          // Count the number of frames received at 20 MHz BW.                                                                                                                                                   
                  input wire                          mibdot1140MHzFrameReceivedCount,          // Count the number of frames received at 40 MHz BW.                                                                                                                                                   
                  input wire                          mibdot1180MHzFrameReceivedCount,          // Count the number of frames received at 80 MHz BW.                                                                                                                                                   
                  input wire                          mibdot11160MHzFrameReceivedCount,         // Count the number of frames received at 160 MHz BW.                                                                                                                                                  
                  input wire                          mibrw20MHzFailedTXOPCount,                // Count the number of attempts made to acquire a 20 MHz TXOP.                                                                                                                                         
                  input wire                          mibrw20MHzSuccessfulTXOPCount,            // Count the number of successful 20 MHz TXOPs.                                                                                                                                                        
                  input wire                          mibrw40MHzFailedTXOPCount,                // Count the number of attempts made to acquire a 40 MHz TXOP.                                                                                                                                         
                  input wire                          mibrw40MHzSuccessfulTXOPCount,            // Count the number of successful 40 MHz TXOPs.                                                                                                                                                        
                  input wire                          mibrw80MHzFailedTXOPCount,                // Count the number of attempts made to acquire a 80 MHz TXOP.                                                                                                                                         
                  input wire                          mibrw80MHzSuccessfulTXOPCount,            // Count the number of successful 80 MHz TXOPs.                                                                                                                                                        
                  input wire                          mibrw160MHzFailedTXOPCount,               // Count the number of attempts made to acquire a 160 MHz TXOP.                                                                                                                                        
                  input wire                          mibrw160MHzSuccessfulTXOPCount,           // Count the number of successful 160 MHz TXOPs.                                                                                                                                                       
                  input wire                          mibrwDynBWDropCount,                      // Count the number of BW drop using dynamic BW management.                                                                                                                                            
                  input wire                          mibrwStaBWFailedCount,                    // Count the number of failure using static BW management.                                                                                                                                             
                  input wire                          mibdot11DualCTSSuccessCount,              // Count the number of times the dual CTS fails.                                                                                                                                                       
                  input wire                          mibdot11STBCCTSSuccessCount,              // Count the number of times the AP does not detect a collision PIFS after transmitting a STBC CTS frame.                                                                                              
                  input wire                          mibdot11STBCCTSFailureCount,              // Count the number of times the AP detects a collision PIFS after transmitting a STBC CTS frame.                                                                                                      
                  input wire                          mibdot11nonSTBCCTSSuccessCount,           // Count the number of times the AP does not detect a collision PIFS after transmitting a non-STBC CTS frame.                                                                                          
                  input wire                          mibdot11nonSTBCCTSFailureCount,           // Count the number of times the AP detects a collision PIFS after transmitting a non-STBC CTS frame.                                                                                                  

                  //$port_g Clock and Reset
                  input wire                          macCoreClk,           // Clock Input
                  input wire                          macCoreClkHardRst_n,  // Hard reset
                  input wire                          macCoreClkSoftRst_n,  // Soft reset
                  
                  //$port_g  TID Index Latched at mib Trigger
                  input wire    [2 :0]                mibTIDIndex,          // If TIDN of the MIB is
                                                                            // set to one then in that case
                                                                            // address given out of RAM
                                                                            // shall be determined from 
                                                                            // mibTIDIndex
                  
                  
                  input wire                           mibTrigger,          // Trigger From MAC to latch
                                                                            // MIB fields at MIB-MAC interface
                  //$port_g Input from RAM
                  input wire [`RW_MIB_DATA_WIDTH-1 :0] mibTableReadData,    // Read Data from RAM
                  
                  
                  //$port_g Input from Host
                  input wire [`RW_MIB_ADDR_WIDTH-1 :0] mibAddr,             // Address From Host
                  input wire                           mibRd,               // Rd Enable signal from host

                  //$port_g Input from register
                  input  wire [9:0]                    mibTableIndex,       // MIB Table Index in the MIB Table that needs to be updated.
                  input  wire                          mibIncrementMode,    // MIB Increment Mode
                                                                            //   When set, the contents of the MIB entry pointed to 
                                                                            //   by the mibTableIndex are incremented by the mibValue.
                                                                            //   When reset, the contents of the MIB entry pointed to 
                                                                            //   by the mibTableIndex are overwritten by the mibValue.
                  
                  input  wire [15:0]                   mibValue,            // MIB Value
                  input  wire                          mibWrite,            // MIB Write
                  output wire                          mibWriteInValid,     // Clear the mibWrite bit
                  output wire                          mibWriteIn,          // mibWrite
                  input  wire                          mibTableReset,       // mibTableReset from host indicating
                                                                            // of mibTableReset bit in
                                                                            // macCntrl1Reg
                  output wire                          mibTableResetIn,     // mibTableResetIn  
                  output wire                          mibTableResetInValid,// Clear the mibTableReset bit
                  
                  //$port_g Output to Host
                  output reg  [`RW_MIB_DATA_WIDTH-1:0] mibRdData,           // Read Data forwarded to Host
                  output wire                          mibBusy,             // Output MIB busy indication to host

                  //$port_g Output to RAM
                  output wire [`RW_MIB_ADDR_WIDTH-1:0] mibTableAddr,        // RAM Address where either
                                                                            // read or write has to be made
                  output wire [`RW_MIB_DATA_WIDTH-1:0] mibTableWriteData,   // Write Data to RAM during write
                                                                            // operation
                  output wire                          mibTableWriteEn,     // Wr enable to RAM
                  output wire                          mibTableEn           // Chip Select  to RAM
                                      
                  );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////


   localparam ZERO_CT = 32'd0;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
   
   wire [`RW_MIB_ADDR_WIDTH-1 :0] mibAddrOut;
   wire [`IncWidth - 1 :0]        mibIncrementCnt;
   wire                           mibHWUpdateStart;
   
   wire                           ramWrEn;
   wire                           ramRdEn;
   wire                           hwUpdate;
   
   wire                           mibTableResetTable;
   wire                           clearEvent;
   
   wire                           ramUpdated;
      
   wire [`RW_MIB_ADDR_WIDTH-1 :0] mibTableArbAddr;
   wire [`RW_MIB_DATA_WIDTH-1 :0] mibTableArbData;

   wire                           mibRamRdEn;    // Rd enable to RAM


    //************Internal Register*****************//
   reg                            mibRamRdEnReg;
   reg                            mibBusyReg;
   
   reg [`RW_MIB_DATA_WIDTH-1 :0] mibTableReadDataCapt;
   reg                           readDataCapt;
//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

  accessArbiter U_accessArbiter(
                                 // Outputs
                                 .ramWrEn                (ramWrEn),
                                 .ramRdEn                (ramRdEn),
                                 .hwUpdate               (hwUpdate),
                                 .mibBusy                (mibBusy),
                                 .mibTableResetTable     (mibTableResetTable),
                                 .clearEvent             (clearEvent),
                                 .mibTableArbAddr        (mibTableArbAddr),
                                 .mibTableArbData        (mibTableArbData), 
                                 
                                 // Inputs
                                 .macCoreClk             (macCoreClk),
                                 .macCoreClkHardRst_n    (macCoreClkHardRst_n),
                                 .macCoreClkSoftRst_n    (macCoreClkSoftRst_n),
                                 .mibTableReadData       (mibTableReadDataCapt),
                                 .mibAddr                (mibAddr),
                                 .mibRd                  (mibRd),
                                 .mibTableIndex          (mibTableIndex),   
                                 .mibIncrementMode       (mibIncrementMode),
                                 .mibValue               (mibValue),       
                                 .mibWrite               (mibWrite),       
                                 .mibWriteInValid        (mibWriteInValid),
                                 .mibWriteIn             (mibWriteIn),     
                                 .mibTableReset          (mibTableReset),
                                 .mibTableResetIn        (mibTableResetIn),
                                 .mibTableResetInValid   (mibTableResetInValid),
                                 .mibHWUpdateStart       (mibHWUpdateStart),
                                 .mibTrigger             (mibTrigger),
                                 
                                 .ramUpdated             (ramUpdated));
    
   


   
   memoryController U_memoryController(
                                       // Outputs
                                       .ramUpdated           (ramUpdated),
                                       .mibTableWriteEn      (mibTableWriteEn),
                                       .mibTableEn           (mibTableEn),
                                       .mibRamRdEn           (mibRamRdEn),
                                                                              
                                       // Inputs
                                       .macCoreClk           (macCoreClk),
                                       .macCoreClkHardRst_n  (macCoreClkHardRst_n),
                                       .macCoreClkSoftRst_n  (macCoreClkSoftRst_n),
                                       .hwUpdate             (hwUpdate),
                                       .ramWrEn              (ramWrEn),
                                       .ramRdEn              (ramRdEn),
                                       .mibTableResetTable   (mibTableResetTable)
                                       );
   

      


   // MUX that select Address and Data which needs to be
   // forwarded to RAM. Selection is made between
   // a) Data and Address from SW and
   // b) Data and Address from dataLatch
   // Control signals from memoryController shall help
   // doing this.

   // MUX for Address:
   // Here mibRamRdEn =  Read Enable Signal to RAM from memoryController
   //      hwUpdate   =  Indicates that HW Update is in process
   //      mibAddrOut =  Active MIB address which needs to be updated in RAM
   //      mibAddr    =  Address obtained from SW
   assign                       mibTableAddr  = (mibRamRdEn || mibTableWriteEn) 
                                               ? (hwUpdate ? mibAddrOut : mibTableArbAddr)
                                               : 8'h00;

   // MUX for Data:
   // Here mibTableWriteData    = Write Data forwarded to RAM
   //      mibTableWriteEn      = Write Enable signal to RAM
   //      hwUpdate             = Indicates that HW update is in process
   //      mibTableReadData     = Data Read out of the RAM
   //      mibIncrementCnt      = Active MIB Increment Count which RAM value needs to be
   //                             incremented
   //      mibTableArbData      = SW write data to be forwarded to RAM
   assign    mibTableWriteData  = (mibTableWriteEn) ? 
                                    (hwUpdate ? 
                                      (mibTableReadDataCapt + {ZERO_CT[`RW_MIB_DATA_WIDTH - `IncWidth - 1:0],mibIncrementCnt}) : 
                                      mibTableArbData) :  
                                    `RW_MIB_DATA_WIDTH'd0;

	// Capture Read data to avoid combinational path between MibRamDataRead and MibRamDataWrite
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          mibTableReadDataCapt <= `RW_MIB_DATA_WIDTH'd0;
        else if (readDataCapt)
          mibTableReadDataCapt <= mibTableReadData;
     end

   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          readDataCapt <= 1'd0;
        else if (mibTableEn && !mibTableWriteEn)
          readDataCapt <= 1'b1;
        else
          readDataCapt <= 1'd0;
     end
       

   // MUX for Data read from RAM
   // Here when MIB is busy as indicated by mibBusy and Read Enable
   // was high to RAM then in very next clock valid data shall be 
   // there on the read bus.
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin

        // condition : macCoreClkHardRst_n
        // source    : power On Reset (active low)
        // set       : its active low signal. set on power
        //             reset
        // result    : resets the flop
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibRamRdEnReg <= 1'b0;
          end

        // condition : macCoreClkSoftRst_n
        // source    : soft or synchronous reset
        // set       : its active high signal. set by
        //             Software
        // result    : resets the flop
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibRamRdEnReg <= 1'b0;
          end
        else
          begin
             mibRamRdEnReg <= mibRamRdEn;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)


   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin

        // condition : macCoreClkHardRst_n
        // source    : power On Reset (active low)
        // set       : its active low signal. set on power
        //             reset
        // result    : resets the flop
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibBusyReg <= 1'b0;
          end

        // condition : macCoreClkSoftRst_n
        // source    : soft or synchronous reset
        // set       : its active high signal. set by
        //             Software
        // result    : resets the flop
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibBusyReg <= 1'b0;
          end
        else
          begin
             mibBusyReg <= mibBusy;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)

   // Below implementation captures the RAM read data.
   // Output ram read data when MIB completes software read process 
   // Other option can be of direct mapping of the data read from memory to the
   // read data lines forwarded to host.
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
   begin
     if(macCoreClkHardRst_n == 1'b0)
       mibRdData <= `RW_MIB_DATA_WIDTH'd0;
     else if (mibBusyReg && mibRamRdEnReg)
       mibRdData <= mibTableReadData;
   end    



dataLatch U_dataLatch(
                      // Inputs from TOP
                     .mibdot11WEPExcludedCount(mibdot11WEPExcludedCount),
                     .mibdot11FCSErrorCount(mibdot11FCSErrorCount),
                     .mibrwRxPHYErrorCount(mibrwRxPHYErrorCount),
                     .mibrwRxFIFOOverflowCount(mibrwRxFIFOOverflowCount),
                     .mibrwTxUnderrunCount(mibrwTxUnderrunCount),
                     .mibrwQosUTransmittedMPDUCount(mibrwQosUTransmittedMPDUCount),
                     .mibrwQosGTransmittedMPDUCount(mibrwQosGTransmittedMPDUCount),
                     .mibdot11QosFailedCount(mibdot11QosFailedCount),
                     .mibdot11QosRetryCount(mibdot11QosRetryCount),
                     .mibdot11QosRTSSuccessCount(mibdot11QosRTSSuccessCount),
                     .mibdot11QosRTSFailureCount(mibdot11QosRTSFailureCount),
                     .mibrwQosACKFailureCount(mibrwQosACKFailureCount),
                     .mibrwQosUReceivedMPDUCount(mibrwQosUReceivedMPDUCount),
                     .mibrwQosGReceivedMPDUCount(mibrwQosGReceivedMPDUCount),
                     .mibrwQosUReceivedOtherMPDU(mibrwQosUReceivedOtherMPDU),
                     .mibdot11QosRetriesReceivedCount(mibdot11QosRetriesReceivedCount),
                     .mibrwUTransmittedAMSDUCount(mibrwUTransmittedAMSDUCount),
                     .mibrwGTransmittedAMSDUCount(mibrwGTransmittedAMSDUCount),
                     .mibdot11FailedAMSDUCount(mibdot11FailedAMSDUCount),
                     .mibdot11RetryAMSDUCount(mibdot11RetryAMSDUCount),
                     .mibdot11TransmittedOctetsInAMSDU(mibdot11TransmittedOctetsInAMSDU),
                     .mibdot11AMSDUAckFailureCount(mibdot11AMSDUAckFailureCount),
                     .mibrwUReceivedAMSDUCount(mibrwUReceivedAMSDUCount),
                     .mibrwGReceivedAMSDUCount(mibrwGReceivedAMSDUCount),
                     .mibrwUReceivedOtherAMSDU(mibrwUReceivedOtherAMSDU),
                     .mibdot11ReceivedOctetsInAMSDUCount(mibdot11ReceivedOctetsInAMSDUCount),
                     .mibdot11TransmittedAMPDUCount(mibdot11TransmittedAMPDUCount),
                     .mibdot11TransmittedMPDUInAMPDUCount(mibdot11TransmittedMPDUInAMPDUCount),
                     .mibdot11TransmittedOctetsInAMPDUCount(mibdot11TransmittedOctetsInAMPDUCount),
                     .mibrwUAMPDUReceivedCount(mibrwUAMPDUReceivedCount),
                     .mibrwGAMPDUReceivedCount(mibrwGAMPDUReceivedCount),
                     .mibrwOtherAMPDUReceivedCount(mibrwOtherAMPDUReceivedCount),
                     .mibdot11MPDUInReceivedAMPDUCount(mibdot11MPDUInReceivedAMPDUCount),
                     .mibdot11ReceivedOctetsInAMPDUCount(mibdot11ReceivedOctetsInAMPDUCount),
                     .mibdot11AMPDUDelimiterCRCErrorCount(mibdot11AMPDUDelimiterCRCErrorCount),
                     .mibdot11ImplicitBARFailureCount(mibdot11ImplicitBARFailureCount),
                     .mibdot11ExplicitBARFailureCount(mibdot11ExplicitBARFailureCount),
                     .mibdot1120MHzFrameTransmittedCount(mibdot1120MHzFrameTransmittedCount),
                     .mibdot1140MHzFrameTransmittedCount(mibdot1140MHzFrameTransmittedCount),
                     .mibdot1180MHzFrameTransmittedCount(mibdot1180MHzFrameTransmittedCount),
                     .mibdot11160MHzFrameTransmittedCount(mibdot11160MHzFrameTransmittedCount),
                     .mibdot1120MHzFrameReceivedCount(mibdot1120MHzFrameReceivedCount),
                     .mibdot1140MHzFrameReceivedCount(mibdot1140MHzFrameReceivedCount),
                     .mibdot1180MHzFrameReceivedCount(mibdot1180MHzFrameReceivedCount),
                     .mibdot11160MHzFrameReceivedCount(mibdot11160MHzFrameReceivedCount),
                     .mibrw20MHzFailedTXOPCount(mibrw20MHzFailedTXOPCount),
                     .mibrw20MHzSuccessfulTXOPCount(mibrw20MHzSuccessfulTXOPCount),
                     .mibrw40MHzFailedTXOPCount(mibrw40MHzFailedTXOPCount),
                     .mibrw40MHzSuccessfulTXOPCount(mibrw40MHzSuccessfulTXOPCount),
                     .mibrw80MHzFailedTXOPCount(mibrw80MHzFailedTXOPCount),
                     .mibrw80MHzSuccessfulTXOPCount(mibrw80MHzSuccessfulTXOPCount),
                     .mibrw160MHzFailedTXOPCount(mibrw160MHzFailedTXOPCount),
                     .mibrw160MHzSuccessfulTXOPCount(mibrw160MHzSuccessfulTXOPCount),
                     .mibrwDynBWDropCount(mibrwDynBWDropCount),
                     .mibrwStaBWFailedCount(mibrwStaBWFailedCount),
                     .mibdot11DualCTSSuccessCount(mibdot11DualCTSSuccessCount),
                     .mibdot11STBCCTSSuccessCount(mibdot11STBCCTSSuccessCount),
                     .mibdot11STBCCTSFailureCount(mibdot11STBCCTSFailureCount),
                     .mibdot11nonSTBCCTSSuccessCount(mibdot11nonSTBCCTSSuccessCount),
                     .mibdot11nonSTBCCTSFailureCount(mibdot11nonSTBCCTSFailureCount),
                         
                      // Inputs
                     .macCoreClk                                    (macCoreClk),
                     .macCoreClkHardRst_n                           (macCoreClkHardRst_n),
                     .macCoreClkSoftRst_n                           (macCoreClkSoftRst_n),
                     .mibTIDIndex                                   (mibTIDIndex[2:0]),
                     .mibTrigger                                    (mibTrigger),
                     .mibTableResetTable                            (mibTableResetTable),
                     .ramUpdated                                    (ramUpdated),
                     .clearEvent                                    (clearEvent),
                     // Outputs
                     
                     .mibAddrOut                                    (mibAddrOut[`RW_MIB_ADDR_WIDTH-1:0]),
                     .mibIncrementCnt                               (mibIncrementCnt[`IncWidth-1:0]),
                     .mibHWUpdateStart                              (mibHWUpdateStart)

                           );

                         
                         
endmodule
