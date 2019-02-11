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
// Description      : This module latches the mib fields exposed at the mib-MAC interface.
//                    This module is sub divided into three different sub sections
//                    a) Field Register sub block - this sub block latches the mib fields 
//                                                  when MAC triggers mib Controller and it
//                                                  clears the mib fields when clearEvent is 
//                                                  is detected.MIB shall be segregated at
//                                                  top level it self hence this module
//                                                  shall be receiving directly segregated
//                                                  MIB fields
//                    b) Event detector sub block - out of all mib fields latched, this sub
//                                                  block detects the mib events which needs to 
//                                                  updated. mib field which needs to be updated
//                                                  shall be represented by non zero value other wise
//                                                  mib fields shall be kept zero by MAC controller.
//                    c) Event Research sub block - This sub block provides the address 
//                                                  of the mib field which needs to be 
//                                                  updated obtained from Event Detector block.
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
// 
// -----------------------------------------------------------------------------
// --
// --
// -----------------------------------------------------------------------------

`include "commonDefines.v"
`include "commonDefine.v"
`include "define.v"
`include "defineAHB.v"
`include "defineDMA.v"


`include "global_define.v"
module dataLatch(
               
                  //$port_g  MIBs input from Top
                 input wire                        mibdot11WEPExcludedCount,                 // Count the number of unencrypted frames that have been discarded.                                                                                                                                    
                 input wire                        mibdot11FCSErrorCount,                    // Count the receive FCS errors.                                                                                                                                                                       
                 input wire                        mibrwRxPHYErrorCount,                     // Count the number of PHY Errors reported during a receive transaction.                                                                                                                               
                 input wire                        mibrwRxFIFOOverflowCount,                 // Count the number of times the Receive FIFO has overflowed.                                                                                                                                          
                 input wire                        mibrwTxUnderrunCount,                     // Count the number of times underrun has occurred on the Transmit side .                                                                                                                              
                 input wire                        mibrwQosUTransmittedMPDUCount,            // Count the number of unicast MPDUs, not containing an A-MSDU, that were transmitted successfully without using BA policy.                                                                            
                 input wire                        mibrwQosGTransmittedMPDUCount,            // Count the number of group-addressed MPDUs, not containing an A-MSDU, that were transmitted successfully.                                                                                            
                 input wire                        mibdot11QosFailedCount,                   // Count the number of MSDUs or MMPDUs that were discarded because of retry-limit-reached condition.                                                                                                   
                 input wire                        mibdot11QosRetryCount,                    // Count the number of unfragmented MSDUs or unfragmented MMPDUs that were transmitted successfully after 1 or more retransmissions without using BA policy.                                           
                 input wire                        mibdot11QosRTSSuccessCount,               // Count the number of successful RTS frame transmissions.                                                                                                                                             
                 input wire                        mibdot11QosRTSFailureCount,               // Count the number of unsuccessful RTS frame transmissions                                                                                                                                            
                 input wire                        mibrwQosACKFailureCount,                  // Count the number of MPDUs, not containing an A-MSDU, that did not receive an ACK frame successfully in response.                                                                                    
                 input wire                        mibrwQosUReceivedMPDUCount,               // Count the number of unicast MPDUs, not containing an A-MSDU, received successfully, destined to this device.                                                                                        
                 input wire                        mibrwQosGReceivedMPDUCount,               // Count the number of group-addressed MPDUs, not containing an A-MSDU, received successfully.                                                                                                         
                 input wire                        mibrwQosUReceivedOtherMPDU,               // Count the number of unicast MPDUs, not containing an A-MSDU, received successfully, not destined to this device.                                                                                    
                 input wire                        mibdot11QosRetriesReceivedCount,          // Count the number of MPDUs that are received with the retry bit set.                                                                                                                                 
                 input wire                        mibrwUTransmittedAMSDUCount,              // Count the number of unicast A-MSDUs that were transmitted successfully without using BA policy.                                                                                                     
                 input wire                        mibrwGTransmittedAMSDUCount,              // Count the number of group-addressed A-MSDUs that were transmitted successfully .                                                                                                                    
                 input wire                        mibdot11FailedAMSDUCount,                 // Count the number of A-MSDUs that were discarded because of retry-limit-reached condition.                                                                                                           
                 input wire                        mibdot11RetryAMSDUCount,                  // Count the number of A-MSDUs that were transmitted successfully after 1 or more retransmissions without using BA policy.                                                                             
                 input wire [15 : 0]               mibdot11TransmittedOctetsInAMSDU,         // Count the number of bytes in the frame body of an A-MSDU that was transmitted successfully without using BA policy .                                                                                
                 input wire                        mibdot11AMSDUAckFailureCount,             // Count the number of A-MSDUs that did not receive an ACK frame successfully in response.                                                                                                             
                 input wire                        mibrwUReceivedAMSDUCount,                 // Count the number of unicast A-MSDUs received successfully, destined to this device.                                                                                                                 
                 input wire                        mibrwGReceivedAMSDUCount,                 // Count the number of group-addressed A-MSDUs received successfully.                                                                                                                                  
                 input wire                        mibrwUReceivedOtherAMSDU,                 // Count the number of unicast A-MSDUs received successfully, not destined to this device.                                                                                                             
                 input wire [15 : 0]               mibdot11ReceivedOctetsInAMSDUCount,       // Count the number of bytes in the frame body of an A-MSDU that was received successfully.                                                                                                            
                 input wire                        mibdot11TransmittedAMPDUCount,            // Count the number of A-MPDUs that were transmitted.                                                                                                                                                  
                 input wire                        mibdot11TransmittedMPDUInAMPDUCount,      // Count the number of MPDUs that were transmitted in an A-MPDU.                                                                                                                                       
                 input wire [15 : 0]               mibdot11TransmittedOctetsInAMPDUCount,    // Count the number of bytes in a transmitted A-MPDU.                                                                                                                                                  
                 input wire                        mibrwUAMPDUReceivedCount,                 // Count the number of unicast A-MPDUs received, destined to this device.                                                                                                                              
                 input wire                        mibrwGAMPDUReceivedCount,                 // Count the number of group-addressed A-MPDUs received.                                                                                                                                               
                 input wire                        mibrwOtherAMPDUReceivedCount,             // Count the number of unicast A-MPDUs received, not destined to this device.                                                                                                                          
                 input wire                        mibdot11MPDUInReceivedAMPDUCount,         // Count the number of MPDUs that were received in an A-MPDU.                                                                                                                                          
                 input wire [15 : 0]               mibdot11ReceivedOctetsInAMPDUCount,       // Count the number of bytes received in an A-MPDU.                                                                                                                                                    
                 input wire [7 : 0]                mibdot11AMPDUDelimiterCRCErrorCount,      // Count the number of CRC errors in MPDU Delimiter of an A-MPDU. An immediately repeated CRC error within an A-MPDU is not counted.                                                                   
                 input wire                        mibdot11ImplicitBARFailureCount,          // Count the number of Implicit BAR frames that did not receive the BA frame successfully in response.                                                                                                 
                 input wire                        mibdot11ExplicitBARFailureCount,          // Count the number of Explicit BAR frames that did not receive the BA frame successfully in response.                                                                                                 
                 input wire                        mibdot1120MHzFrameTransmittedCount,       // Count the number of frames transmitted at 20 MHz BW.                                                                                                                                                
                 input wire                        mibdot1140MHzFrameTransmittedCount,       // Count the number of frames transmitted at 40 MHz BW.                                                                                                                                                
                 input wire                        mibdot1180MHzFrameTransmittedCount,       // Count the number of frames transmitted at 80 MHz BW.                                                                                                                                                
                 input wire                        mibdot11160MHzFrameTransmittedCount,      // Count the number of frames transmitted at 160 MHz BW.                                                                                                                                               
                 input wire                        mibdot1120MHzFrameReceivedCount,          // Count the number of frames received at 20 MHz BW.                                                                                                                                                   
                 input wire                        mibdot1140MHzFrameReceivedCount,          // Count the number of frames received at 40 MHz BW.                                                                                                                                                   
                 input wire                        mibdot1180MHzFrameReceivedCount,          // Count the number of frames received at 80 MHz BW.                                                                                                                                                   
                 input wire                        mibdot11160MHzFrameReceivedCount,         // Count the number of frames received at 160 MHz BW.                                                                                                                                                  
                 input wire                        mibrw20MHzFailedTXOPCount,                // Count the number of attempts made to acquire a 20 MHz TXOP.                                                                                                                                         
                 input wire                        mibrw20MHzSuccessfulTXOPCount,            // Count the number of successful 20 MHz TXOPs.                                                                                                                                                        
                 input wire                        mibrw40MHzFailedTXOPCount,                // Count the number of attempts made to acquire a 40 MHz TXOP.                                                                                                                                         
                 input wire                        mibrw40MHzSuccessfulTXOPCount,            // Count the number of successful 40 MHz TXOPs.                                                                                                                                                        
                 input wire                        mibrw80MHzFailedTXOPCount,                // Count the number of attempts made to acquire a 80 MHz TXOP.                                                                                                                                         
                 input wire                        mibrw80MHzSuccessfulTXOPCount,            // Count the number of successful 80 MHz TXOPs.                                                                                                                                                        
                 input wire                        mibrw160MHzFailedTXOPCount,               // Count the number of attempts made to acquire a 160 MHz TXOP.                                                                                                                                        
                 input wire                        mibrw160MHzSuccessfulTXOPCount,           // Count the number of successful 160 MHz TXOPs.                                                                                                                                                       
                 input wire                        mibrwDynBWDropCount,                      // Count the number of BW drop using dynamic BW management.                                                                                                                                            
                 input wire                        mibrwStaBWFailedCount,                    // Count the number of failure using static BW management.                                                                                                                                             
                 input wire                        mibdot11DualCTSSuccessCount,              // Count the number of times the dual CTS fails.                                                                                                                                                       
                 input wire                        mibdot11STBCCTSSuccessCount,              // Count the number of times the AP does not detect a collision PIFS after transmitting a STBC CTS frame.                                                                                              
                 input wire                        mibdot11STBCCTSFailureCount,              // Count the number of times the AP detects a collision PIFS after transmitting a STBC CTS frame.                                                                                                      
                 input wire                        mibdot11nonSTBCCTSSuccessCount,           // Count the number of times the AP does not detect a collision PIFS after transmitting a non-STBC CTS frame.                                                                                          
                 input wire                        mibdot11nonSTBCCTSFailureCount,           // Count the number of times the AP detects a collision PIFS after transmitting a non-STBC CTS frame.                                                                                                  
                 
                 //$port_g Clock and Reset Input
                 input wire                        macCoreClk,
                 input wire                        macCoreClkHardRst_n,
                 input wire                        macCoreClkSoftRst_n,
                 
                 
                 //$port_g  Control
                 input wire [2 :0]                 mibTIDIndex,       // If TIDN of the MIB is
                                                                       // set to one then in that case
                                                                       // address given out of RAM
                                                                       // shall be determined from mibTIDIndex
   
                 
                 input wire                         mibTrigger,        // mibTrigger from MAC Controller

                 input wire                         mibTableResetTable,// Indicates that reset bit in 
                                                                       // mac control reg is set and 
                                                                       // MIB needs to reset whole MIB 
                                                                       // Table by writting zero in 
                                                                       // every location in RAM.
   
                 
                 input wire                         ramUpdated,        // ram updated indication from 
                                                                       // memorycontroller
                 
                 input wire                         clearEvent,        // clear event indication.

                 //$port_g  OUTPUT FROM dataLatch
                 output wire [`RW_MIB_ADDR_WIDTH-1 :0] mibAddrOut,     // address of the active MIB which
                                                                       // needs to be updated. Output
                                                                       // to accessArbiter.
   
                 output reg [`IncWidth-1 : 0]       mibIncrementCnt,   // increment cnt by which active
                                                                       // mib needs to be updated in ram
                 output reg                         mibHWUpdateStart   // indicates that mib update is over
                 
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////




  // mibdot11WEPExcludedCount1                               
  localparam ADDRESSMIB1_CT = 8'h00; 
  // mibdot11FCSErrorCount2                               
  localparam ADDRESSMIB2_CT = 8'h01; 
  // mibrwRxPHYErrorCount3                               
  localparam ADDRESSMIB3_CT = 8'h02; 
  // mibrwRxFIFOOverflowCount4                               
  localparam ADDRESSMIB4_CT = 8'h03; 
  // mibrwTxUnderrunCount5                               
  localparam ADDRESSMIB5_CT = 8'h04; 
  // mibrwQosUTransmittedMPDUCount6                               
  localparam ADDRESSMIB6_CT = 8'h0C; 
  // mibrwQosGTransmittedMPDUCount7                               
  localparam ADDRESSMIB7_CT = 8'h14; 
  // mibdot11QosFailedCount8                               
  localparam ADDRESSMIB8_CT = 8'h1C; 
  // mibdot11QosRetryCount9                               
  localparam ADDRESSMIB9_CT = 8'h24; 
  // mibdot11QosRTSSuccessCount10                               
  localparam ADDRESSMIB10_CT = 8'h2C; 
  // mibdot11QosRTSFailureCount11                               
  localparam ADDRESSMIB11_CT = 8'h34; 
  // mibrwQosACKFailureCount12                               
  localparam ADDRESSMIB12_CT = 8'h3C; 
  // mibrwQosUReceivedMPDUCount13                               
  localparam ADDRESSMIB13_CT = 8'h44; 
  // mibrwQosGReceivedMPDUCount14                               
  localparam ADDRESSMIB14_CT = 8'h4C; 
  // mibrwQosUReceivedOtherMPDU15                               
  localparam ADDRESSMIB15_CT = 8'h54; 
  // mibdot11QosRetriesReceivedCount16                               
  localparam ADDRESSMIB16_CT = 8'h5C; 
  // mibrwUTransmittedAMSDUCount17                               
  localparam ADDRESSMIB17_CT = 8'h64; 
  // mibrwGTransmittedAMSDUCount18                               
  localparam ADDRESSMIB18_CT = 8'h6C; 
  // mibdot11FailedAMSDUCount19                               
  localparam ADDRESSMIB19_CT = 8'h74; 
  // mibdot11RetryAMSDUCount20                               
  localparam ADDRESSMIB20_CT = 8'h7C; 
  // mibdot11TransmittedOctetsInAMSDU21                               
  localparam ADDRESSMIB21_CT = 8'h84; 
  // mibdot11AMSDUAckFailureCount22                               
  localparam ADDRESSMIB22_CT = 8'h8C; 
  // mibrwUReceivedAMSDUCount23                               
  localparam ADDRESSMIB23_CT = 8'h94; 
  // mibrwGReceivedAMSDUCount24                               
  localparam ADDRESSMIB24_CT = 8'h9C; 
  // mibrwUReceivedOtherAMSDU25                               
  localparam ADDRESSMIB25_CT = 8'hA4; 
  // mibdot11ReceivedOctetsInAMSDUCount26                               
  localparam ADDRESSMIB26_CT = 8'hAC; 
  // mibdot11TransmittedAMPDUCount27                               
  localparam ADDRESSMIB27_CT = 8'hCC; 
  // mibdot11TransmittedMPDUInAMPDUCount28                               
  localparam ADDRESSMIB28_CT = 8'hCD; 
  // mibdot11TransmittedOctetsInAMPDUCount29                               
  localparam ADDRESSMIB29_CT = 8'hCE; 
  // mibrwUAMPDUReceivedCount30                               
  localparam ADDRESSMIB30_CT = 8'hCF; 
  // mibrwGAMPDUReceivedCount31                               
  localparam ADDRESSMIB31_CT = 8'hD0; 
  // mibrwOtherAMPDUReceivedCount32                               
  localparam ADDRESSMIB32_CT = 8'hD1; 
  // mibdot11MPDUInReceivedAMPDUCount33                               
  localparam ADDRESSMIB33_CT = 8'hD2; 
  // mibdot11ReceivedOctetsInAMPDUCount34                               
  localparam ADDRESSMIB34_CT = 8'hD3; 
  // mibdot11AMPDUDelimiterCRCErrorCount35                               
  localparam ADDRESSMIB35_CT = 8'hD4; 
  // mibdot11ImplicitBARFailureCount36                               
  localparam ADDRESSMIB36_CT = 8'hD5; 
  // mibdot11ExplicitBARFailureCount37                               
  localparam ADDRESSMIB37_CT = 8'hD6; 
  // mibdot1120MHzFrameTransmittedCount38                               
  localparam ADDRESSMIB38_CT = 8'hDC; 
  // mibdot1140MHzFrameTransmittedCount39                               
  localparam ADDRESSMIB39_CT = 8'hDD; 
  // mibdot1180MHzFrameTransmittedCount40                               
  localparam ADDRESSMIB40_CT = 8'hDE; 
  // mibdot11160MHzFrameTransmittedCount41                               
  localparam ADDRESSMIB41_CT = 8'hDF; 
  // mibdot1120MHzFrameReceivedCount42                               
  localparam ADDRESSMIB42_CT = 8'hE0; 
  // mibdot1140MHzFrameReceivedCount43                               
  localparam ADDRESSMIB43_CT = 8'hE1; 
  // mibdot1180MHzFrameReceivedCount44                               
  localparam ADDRESSMIB44_CT = 8'hE2; 
  // mibdot11160MHzFrameReceivedCount45                               
  localparam ADDRESSMIB45_CT = 8'hE3; 
  // mibrw20MHzFailedTXOPCount46                               
  localparam ADDRESSMIB46_CT = 8'hE4; 
  // mibrw20MHzSuccessfulTXOPCount47                               
  localparam ADDRESSMIB47_CT = 8'hE5; 
  // mibrw40MHzFailedTXOPCount48                               
  localparam ADDRESSMIB48_CT = 8'hE6; 
  // mibrw40MHzSuccessfulTXOPCount49                               
  localparam ADDRESSMIB49_CT = 8'hE7; 
  // mibrw80MHzFailedTXOPCount50                               
  localparam ADDRESSMIB50_CT = 8'hE8; 
  // mibrw80MHzSuccessfulTXOPCount51                               
  localparam ADDRESSMIB51_CT = 8'hE9; 
  // mibrw160MHzFailedTXOPCount52                               
  localparam ADDRESSMIB52_CT = 8'hEA; 
  // mibrw160MHzSuccessfulTXOPCount53                               
  localparam ADDRESSMIB53_CT = 8'hEB; 
  // mibrwDynBWDropCount54                               
  localparam ADDRESSMIB54_CT = 8'hEC; 
  // mibrwStaBWFailedCount55                               
  localparam ADDRESSMIB55_CT = 8'hED; 
  // mibdot11DualCTSSuccessCount56                               
  localparam ADDRESSMIB56_CT = 8'hF0; 
  // mibdot11STBCCTSSuccessCount57                               
  localparam ADDRESSMIB57_CT = 8'hF1; 
  // mibdot11STBCCTSFailureCount58                               
  localparam ADDRESSMIB58_CT = 8'hF2; 
  // mibdot11nonSTBCCTSSuccessCount59                               
  localparam ADDRESSMIB59_CT = 8'hF3; 
  // mibdot11nonSTBCCTSFailureCount60                               
  localparam ADDRESSMIB60_CT = 8'hF4; 
localparam ZERO_CT = 32'd0;
  

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// **************Internal wires********************//
wire [2 : 0]                     tidIndexIn;                     

wire [`TotalMIBDefined-1 : 0]    mibReg;                         // Stores all MIB Events latched
                                                                 // during mibTrigger
 
// **************Internal Register**********************//
reg [`RW_MIB_ADDR_WIDTH-1 : 0]  mibAddrOutRawInt;

reg [`IncWidth - 1 : 0]         mibIncrementCntRaw;       
reg                             mibTriggerDD;             
reg                             mibTriggerD;              

reg                             mibCurrAddrOutSearchNext; 
reg [`RW_MIB_INDEX_WIDTH-1 : 0] mibIndexCurrentFF;        
reg [`RW_MIB_WINDOW_WIDTH-1: 0] nextMibIndexCurrent;      

reg                             shiftMibWindow;           

reg                             shiftMibWindowReg;        

reg [`RW_MIB_INDEX_WIDTH-1 : 0] mibIndexNext;             
reg [`RW_MIB_INDEX_WIDTH-1 : 0] mibIndexCurrent;          

reg [`TotalMIBDefined-1 : 0]    shiftMibFieldReg;         

reg [`ShiftWindowCnt-1 : 0]     windowShiftCnt;           



reg [2 : 0]                     tidIndexReg;              

reg [2 : 0]                     tidIndexInt;              


reg [`RW_MIB_WINDOW_WIDTH-1: 0] incCounter;               
 
// Integer used for "for" loop
integer                      i;
   
   
                                                  

// Internal Wires And Registers for mibdot11WEPExcludedCount
wire       mibdot11WEPExcludedCountIn;
reg        mibdot11WEPExcludedCountReg;

// Internal Wires And Registers for mibdot11FCSErrorCount
wire       mibdot11FCSErrorCountIn;
reg        mibdot11FCSErrorCountReg;

// Internal Wires And Registers for mibrwRxPHYErrorCount
wire       mibrwRxPHYErrorCountIn;
reg        mibrwRxPHYErrorCountReg;

// Internal Wires And Registers for mibrwRxFIFOOverflowCount
wire       mibrwRxFIFOOverflowCountIn;
reg        mibrwRxFIFOOverflowCountReg;

// Internal Wires And Registers for mibrwTxUnderrunCount
wire       mibrwTxUnderrunCountIn;
reg        mibrwTxUnderrunCountReg;

// Internal Wires And Registers for mibrwQosUTransmittedMPDUCount
wire       mibrwQosUTransmittedMPDUCountIn;
reg        mibrwQosUTransmittedMPDUCountReg;

// Internal Wires And Registers for mibrwQosGTransmittedMPDUCount
wire       mibrwQosGTransmittedMPDUCountIn;
reg        mibrwQosGTransmittedMPDUCountReg;

// Internal Wires And Registers for mibdot11QosFailedCount
wire       mibdot11QosFailedCountIn;
reg        mibdot11QosFailedCountReg;

// Internal Wires And Registers for mibdot11QosRetryCount
wire       mibdot11QosRetryCountIn;
reg        mibdot11QosRetryCountReg;

// Internal Wires And Registers for mibdot11QosRTSSuccessCount
wire       mibdot11QosRTSSuccessCountIn;
reg        mibdot11QosRTSSuccessCountReg;

// Internal Wires And Registers for mibdot11QosRTSFailureCount
wire       mibdot11QosRTSFailureCountIn;
reg        mibdot11QosRTSFailureCountReg;

// Internal Wires And Registers for mibrwQosACKFailureCount
wire       mibrwQosACKFailureCountIn;
reg        mibrwQosACKFailureCountReg;

// Internal Wires And Registers for mibrwQosUReceivedMPDUCount
wire       mibrwQosUReceivedMPDUCountIn;
reg        mibrwQosUReceivedMPDUCountReg;

// Internal Wires And Registers for mibrwQosGReceivedMPDUCount
wire       mibrwQosGReceivedMPDUCountIn;
reg        mibrwQosGReceivedMPDUCountReg;

// Internal Wires And Registers for mibrwQosUReceivedOtherMPDU
wire       mibrwQosUReceivedOtherMPDUIn;
reg        mibrwQosUReceivedOtherMPDUReg;

// Internal Wires And Registers for mibdot11QosRetriesReceivedCount
wire       mibdot11QosRetriesReceivedCountIn;
reg        mibdot11QosRetriesReceivedCountReg;

// Internal Wires And Registers for mibrwUTransmittedAMSDUCount
wire       mibrwUTransmittedAMSDUCountIn;
reg        mibrwUTransmittedAMSDUCountReg;

// Internal Wires And Registers for mibrwGTransmittedAMSDUCount
wire       mibrwGTransmittedAMSDUCountIn;
reg        mibrwGTransmittedAMSDUCountReg;

// Internal Wires And Registers for mibdot11FailedAMSDUCount
wire       mibdot11FailedAMSDUCountIn;
reg        mibdot11FailedAMSDUCountReg;

// Internal Wires And Registers for mibdot11RetryAMSDUCount
wire       mibdot11RetryAMSDUCountIn;
reg        mibdot11RetryAMSDUCountReg;

// Internal Wires And Registers for mibdot11TransmittedOctetsInAMSDU
wire [15 : 0] mibdot11TransmittedOctetsInAMSDUIn;
reg  [15 : 0] mibdot11TransmittedOctetsInAMSDUReg;

// Internal Wires And Registers for mibdot11AMSDUAckFailureCount
wire       mibdot11AMSDUAckFailureCountIn;
reg        mibdot11AMSDUAckFailureCountReg;

// Internal Wires And Registers for mibrwUReceivedAMSDUCount
wire       mibrwUReceivedAMSDUCountIn;
reg        mibrwUReceivedAMSDUCountReg;

// Internal Wires And Registers for mibrwGReceivedAMSDUCount
wire       mibrwGReceivedAMSDUCountIn;
reg        mibrwGReceivedAMSDUCountReg;

// Internal Wires And Registers for mibrwUReceivedOtherAMSDU
wire       mibrwUReceivedOtherAMSDUIn;
reg        mibrwUReceivedOtherAMSDUReg;

// Internal Wires And Registers for mibdot11ReceivedOctetsInAMSDUCount
wire [15 : 0] mibdot11ReceivedOctetsInAMSDUCountIn;
reg  [15 : 0] mibdot11ReceivedOctetsInAMSDUCountReg;

// Internal Wires And Registers for mibdot11TransmittedAMPDUCount
wire       mibdot11TransmittedAMPDUCountIn;
reg        mibdot11TransmittedAMPDUCountReg;

// Internal Wires And Registers for mibdot11TransmittedMPDUInAMPDUCount
wire       mibdot11TransmittedMPDUInAMPDUCountIn;
reg        mibdot11TransmittedMPDUInAMPDUCountReg;

// Internal Wires And Registers for mibdot11TransmittedOctetsInAMPDUCount
wire [15 : 0] mibdot11TransmittedOctetsInAMPDUCountIn;
reg  [15 : 0] mibdot11TransmittedOctetsInAMPDUCountReg;

// Internal Wires And Registers for mibrwUAMPDUReceivedCount
wire       mibrwUAMPDUReceivedCountIn;
reg        mibrwUAMPDUReceivedCountReg;

// Internal Wires And Registers for mibrwGAMPDUReceivedCount
wire       mibrwGAMPDUReceivedCountIn;
reg        mibrwGAMPDUReceivedCountReg;

// Internal Wires And Registers for mibrwOtherAMPDUReceivedCount
wire       mibrwOtherAMPDUReceivedCountIn;
reg        mibrwOtherAMPDUReceivedCountReg;

// Internal Wires And Registers for mibdot11MPDUInReceivedAMPDUCount
wire       mibdot11MPDUInReceivedAMPDUCountIn;
reg        mibdot11MPDUInReceivedAMPDUCountReg;

// Internal Wires And Registers for mibdot11ReceivedOctetsInAMPDUCount
wire [15 : 0] mibdot11ReceivedOctetsInAMPDUCountIn;
reg  [15 : 0] mibdot11ReceivedOctetsInAMPDUCountReg;

// Internal Wires And Registers for mibdot11AMPDUDelimiterCRCErrorCount
wire [7 : 0] mibdot11AMPDUDelimiterCRCErrorCountIn;
reg  [7 : 0] mibdot11AMPDUDelimiterCRCErrorCountReg;

// Internal Wires And Registers for mibdot11ImplicitBARFailureCount
wire       mibdot11ImplicitBARFailureCountIn;
reg        mibdot11ImplicitBARFailureCountReg;

// Internal Wires And Registers for mibdot11ExplicitBARFailureCount
wire       mibdot11ExplicitBARFailureCountIn;
reg        mibdot11ExplicitBARFailureCountReg;

// Internal Wires And Registers for mibdot1120MHzFrameTransmittedCount
wire       mibdot1120MHzFrameTransmittedCountIn;
reg        mibdot1120MHzFrameTransmittedCountReg;

// Internal Wires And Registers for mibdot1140MHzFrameTransmittedCount
wire       mibdot1140MHzFrameTransmittedCountIn;
reg        mibdot1140MHzFrameTransmittedCountReg;

// Internal Wires And Registers for mibdot1180MHzFrameTransmittedCount
wire       mibdot1180MHzFrameTransmittedCountIn;
reg        mibdot1180MHzFrameTransmittedCountReg;

// Internal Wires And Registers for mibdot11160MHzFrameTransmittedCount
wire       mibdot11160MHzFrameTransmittedCountIn;
reg        mibdot11160MHzFrameTransmittedCountReg;

// Internal Wires And Registers for mibdot1120MHzFrameReceivedCount
wire       mibdot1120MHzFrameReceivedCountIn;
reg        mibdot1120MHzFrameReceivedCountReg;

// Internal Wires And Registers for mibdot1140MHzFrameReceivedCount
wire       mibdot1140MHzFrameReceivedCountIn;
reg        mibdot1140MHzFrameReceivedCountReg;

// Internal Wires And Registers for mibdot1180MHzFrameReceivedCount
wire       mibdot1180MHzFrameReceivedCountIn;
reg        mibdot1180MHzFrameReceivedCountReg;

// Internal Wires And Registers for mibdot11160MHzFrameReceivedCount
wire       mibdot11160MHzFrameReceivedCountIn;
reg        mibdot11160MHzFrameReceivedCountReg;

// Internal Wires And Registers for mibrw20MHzFailedTXOPCount
wire       mibrw20MHzFailedTXOPCountIn;
reg        mibrw20MHzFailedTXOPCountReg;

// Internal Wires And Registers for mibrw20MHzSuccessfulTXOPCount
wire       mibrw20MHzSuccessfulTXOPCountIn;
reg        mibrw20MHzSuccessfulTXOPCountReg;

// Internal Wires And Registers for mibrw40MHzFailedTXOPCount
wire       mibrw40MHzFailedTXOPCountIn;
reg        mibrw40MHzFailedTXOPCountReg;

// Internal Wires And Registers for mibrw40MHzSuccessfulTXOPCount
wire       mibrw40MHzSuccessfulTXOPCountIn;
reg        mibrw40MHzSuccessfulTXOPCountReg;

// Internal Wires And Registers for mibrw80MHzFailedTXOPCount
wire       mibrw80MHzFailedTXOPCountIn;
reg        mibrw80MHzFailedTXOPCountReg;

// Internal Wires And Registers for mibrw80MHzSuccessfulTXOPCount
wire       mibrw80MHzSuccessfulTXOPCountIn;
reg        mibrw80MHzSuccessfulTXOPCountReg;

// Internal Wires And Registers for mibrw160MHzFailedTXOPCount
wire       mibrw160MHzFailedTXOPCountIn;
reg        mibrw160MHzFailedTXOPCountReg;

// Internal Wires And Registers for mibrw160MHzSuccessfulTXOPCount
wire       mibrw160MHzSuccessfulTXOPCountIn;
reg        mibrw160MHzSuccessfulTXOPCountReg;

// Internal Wires And Registers for mibrwDynBWDropCount
wire       mibrwDynBWDropCountIn;
reg        mibrwDynBWDropCountReg;

// Internal Wires And Registers for mibrwStaBWFailedCount
wire       mibrwStaBWFailedCountIn;
reg        mibrwStaBWFailedCountReg;

// Internal Wires And Registers for mibdot11DualCTSSuccessCount
wire       mibdot11DualCTSSuccessCountIn;
reg        mibdot11DualCTSSuccessCountReg;

// Internal Wires And Registers for mibdot11STBCCTSSuccessCount
wire       mibdot11STBCCTSSuccessCountIn;
reg        mibdot11STBCCTSSuccessCountReg;

// Internal Wires And Registers for mibdot11STBCCTSFailureCount
wire       mibdot11STBCCTSFailureCountIn;
reg        mibdot11STBCCTSFailureCountReg;

// Internal Wires And Registers for mibdot11nonSTBCCTSSuccessCount
wire       mibdot11nonSTBCCTSSuccessCountIn;
reg        mibdot11nonSTBCCTSSuccessCountReg;

// Internal Wires And Registers for mibdot11nonSTBCCTSFailureCount
wire       mibdot11nonSTBCCTSFailureCountIn;
reg        mibdot11nonSTBCCTSFailureCountReg;
                                                  
                                                  
                                                  
   /////////////////////////////////////////
   // Beginning of the Logic
   ////////////////////////////////////////
   
   
   // a) Field Register sub block:
   // Begins


   // Latching of mib Fields exposed at the mib-MAC Controller and which are segregated
   // at top level module. MIB fields get cleared on the clear events
   // Clear Events get set to one when either
   // a) HW Update is interrupted by SW operation (SW Read or Write)
   // b) Reset Table is initiated

   // Latching of mib Fields exposed at the mib-MAC Controller and which are segregated
   // at top level module.
   
   
                                                  
assign       mibdot11WEPExcludedCountIn   =    (mibTrigger ?
                             (mibdot11WEPExcludedCount)
                            :((clearEvent) ?  1'h0  : mibdot11WEPExcludedCountReg));
                                                                
assign       mibdot11FCSErrorCountIn   =    (mibTrigger ?
                             (mibdot11FCSErrorCount)
                            :((clearEvent) ?  1'h0  : mibdot11FCSErrorCountReg));
                                                                
assign       mibrwRxPHYErrorCountIn   =    (mibTrigger ?
                             (mibrwRxPHYErrorCount)
                            :((clearEvent) ?  1'h0  : mibrwRxPHYErrorCountReg));
                                                                
assign       mibrwRxFIFOOverflowCountIn   =    (mibTrigger ?
                             (mibrwRxFIFOOverflowCount)
                            :((clearEvent) ?  1'h0  : mibrwRxFIFOOverflowCountReg));
                                                                
assign       mibrwTxUnderrunCountIn   =    (mibTrigger ?
                             (mibrwTxUnderrunCount)
                            :((clearEvent) ?  1'h0  : mibrwTxUnderrunCountReg));
                                                                
assign       mibrwQosUTransmittedMPDUCountIn   =    (mibTrigger ?
                             (mibrwQosUTransmittedMPDUCount)
                            :((clearEvent) ?  1'h0  : mibrwQosUTransmittedMPDUCountReg));
                                                                
assign       mibrwQosGTransmittedMPDUCountIn   =    (mibTrigger ?
                             (mibrwQosGTransmittedMPDUCount)
                            :((clearEvent) ?  1'h0  : mibrwQosGTransmittedMPDUCountReg));
                                                                
assign       mibdot11QosFailedCountIn   =    (mibTrigger ?
                             (mibdot11QosFailedCount)
                            :((clearEvent) ?  1'h0  : mibdot11QosFailedCountReg));
                                                                
assign       mibdot11QosRetryCountIn   =    (mibTrigger ?
                             (mibdot11QosRetryCount)
                            :((clearEvent) ?  1'h0  : mibdot11QosRetryCountReg));
                                                                
assign       mibdot11QosRTSSuccessCountIn   =    (mibTrigger ?
                             (mibdot11QosRTSSuccessCount)
                            :((clearEvent) ?  1'h0  : mibdot11QosRTSSuccessCountReg));
                                                                
assign       mibdot11QosRTSFailureCountIn   =    (mibTrigger ?
                             (mibdot11QosRTSFailureCount)
                            :((clearEvent) ?  1'h0  : mibdot11QosRTSFailureCountReg));
                                                                
assign       mibrwQosACKFailureCountIn   =    (mibTrigger ?
                             (mibrwQosACKFailureCount)
                            :((clearEvent) ?  1'h0  : mibrwQosACKFailureCountReg));
                                                                
assign       mibrwQosUReceivedMPDUCountIn   =    (mibTrigger ?
                             (mibrwQosUReceivedMPDUCount)
                            :((clearEvent) ?  1'h0  : mibrwQosUReceivedMPDUCountReg));
                                                                
assign       mibrwQosGReceivedMPDUCountIn   =    (mibTrigger ?
                             (mibrwQosGReceivedMPDUCount)
                            :((clearEvent) ?  1'h0  : mibrwQosGReceivedMPDUCountReg));
                                                                
assign       mibrwQosUReceivedOtherMPDUIn   =    (mibTrigger ?
                             (mibrwQosUReceivedOtherMPDU)
                            :((clearEvent) ?  1'h0  : mibrwQosUReceivedOtherMPDUReg));
                                                                
assign       mibdot11QosRetriesReceivedCountIn   =    (mibTrigger ?
                             (mibdot11QosRetriesReceivedCount)
                            :((clearEvent) ?  1'h0  : mibdot11QosRetriesReceivedCountReg));
                                                                
assign       mibrwUTransmittedAMSDUCountIn   =    (mibTrigger ?
                             (mibrwUTransmittedAMSDUCount)
                            :((clearEvent) ?  1'h0  : mibrwUTransmittedAMSDUCountReg));
                                                                
assign       mibrwGTransmittedAMSDUCountIn   =    (mibTrigger ?
                             (mibrwGTransmittedAMSDUCount)
                            :((clearEvent) ?  1'h0  : mibrwGTransmittedAMSDUCountReg));
                                                                
assign       mibdot11FailedAMSDUCountIn   =    (mibTrigger ?
                             (mibdot11FailedAMSDUCount)
                            :((clearEvent) ?  1'h0  : mibdot11FailedAMSDUCountReg));
                                                                
assign       mibdot11RetryAMSDUCountIn   =    (mibTrigger ?
                             (mibdot11RetryAMSDUCount)
                            :((clearEvent) ?  1'h0  : mibdot11RetryAMSDUCountReg));
                                                                
assign       mibdot11TransmittedOctetsInAMSDUIn   =    (mibTrigger ?
                             (mibdot11TransmittedOctetsInAMSDU)
                            :((clearEvent) ?  16'h0  : mibdot11TransmittedOctetsInAMSDUReg));
                                                                
assign       mibdot11AMSDUAckFailureCountIn   =    (mibTrigger ?
                             (mibdot11AMSDUAckFailureCount)
                            :((clearEvent) ?  1'h0  : mibdot11AMSDUAckFailureCountReg));
                                                                
assign       mibrwUReceivedAMSDUCountIn   =    (mibTrigger ?
                             (mibrwUReceivedAMSDUCount)
                            :((clearEvent) ?  1'h0  : mibrwUReceivedAMSDUCountReg));
                                                                
assign       mibrwGReceivedAMSDUCountIn   =    (mibTrigger ?
                             (mibrwGReceivedAMSDUCount)
                            :((clearEvent) ?  1'h0  : mibrwGReceivedAMSDUCountReg));
                                                                
assign       mibrwUReceivedOtherAMSDUIn   =    (mibTrigger ?
                             (mibrwUReceivedOtherAMSDU)
                            :((clearEvent) ?  1'h0  : mibrwUReceivedOtherAMSDUReg));
                                                                
assign       mibdot11ReceivedOctetsInAMSDUCountIn   =    (mibTrigger ?
                             (mibdot11ReceivedOctetsInAMSDUCount)
                            :((clearEvent) ?  16'h0  : mibdot11ReceivedOctetsInAMSDUCountReg));
                                                                
assign       mibdot11TransmittedAMPDUCountIn   =    (mibTrigger ?
                             (mibdot11TransmittedAMPDUCount)
                            :((clearEvent) ?  1'h0  : mibdot11TransmittedAMPDUCountReg));
                                                                
assign       mibdot11TransmittedMPDUInAMPDUCountIn   =    (mibTrigger ?
                             (mibdot11TransmittedMPDUInAMPDUCount)
                            :((clearEvent) ?  1'h0  : mibdot11TransmittedMPDUInAMPDUCountReg));
                                                                
assign       mibdot11TransmittedOctetsInAMPDUCountIn   =    (mibTrigger ?
                             (mibdot11TransmittedOctetsInAMPDUCount)
                            :((clearEvent) ?  16'h0  : mibdot11TransmittedOctetsInAMPDUCountReg));
                                                                
assign       mibrwUAMPDUReceivedCountIn   =    (mibTrigger ?
                             (mibrwUAMPDUReceivedCount)
                            :((clearEvent) ?  1'h0  : mibrwUAMPDUReceivedCountReg));
                                                                
assign       mibrwGAMPDUReceivedCountIn   =    (mibTrigger ?
                             (mibrwGAMPDUReceivedCount)
                            :((clearEvent) ?  1'h0  : mibrwGAMPDUReceivedCountReg));
                                                                
assign       mibrwOtherAMPDUReceivedCountIn   =    (mibTrigger ?
                             (mibrwOtherAMPDUReceivedCount)
                            :((clearEvent) ?  1'h0  : mibrwOtherAMPDUReceivedCountReg));
                                                                
assign       mibdot11MPDUInReceivedAMPDUCountIn   =    (mibTrigger ?
                             (mibdot11MPDUInReceivedAMPDUCount)
                            :((clearEvent) ?  1'h0  : mibdot11MPDUInReceivedAMPDUCountReg));
                                                                
assign       mibdot11ReceivedOctetsInAMPDUCountIn   =    (mibTrigger ?
                             (mibdot11ReceivedOctetsInAMPDUCount)
                            :((clearEvent) ?  16'h0  : mibdot11ReceivedOctetsInAMPDUCountReg));
                                                                
assign       mibdot11AMPDUDelimiterCRCErrorCountIn   =    (mibTrigger ?
                             (mibdot11AMPDUDelimiterCRCErrorCount)
                            :((clearEvent) ?  8'h0  : mibdot11AMPDUDelimiterCRCErrorCountReg));
                                                                
assign       mibdot11ImplicitBARFailureCountIn   =    (mibTrigger ?
                             (mibdot11ImplicitBARFailureCount)
                            :((clearEvent) ?  1'h0  : mibdot11ImplicitBARFailureCountReg));
                                                                
assign       mibdot11ExplicitBARFailureCountIn   =    (mibTrigger ?
                             (mibdot11ExplicitBARFailureCount)
                            :((clearEvent) ?  1'h0  : mibdot11ExplicitBARFailureCountReg));
                                                                
assign       mibdot1120MHzFrameTransmittedCountIn   =    (mibTrigger ?
                             (mibdot1120MHzFrameTransmittedCount)
                            :((clearEvent) ?  1'h0  : mibdot1120MHzFrameTransmittedCountReg));
                                                                
assign       mibdot1140MHzFrameTransmittedCountIn   =    (mibTrigger ?
                             (mibdot1140MHzFrameTransmittedCount)
                            :((clearEvent) ?  1'h0  : mibdot1140MHzFrameTransmittedCountReg));
                                                                
assign       mibdot1180MHzFrameTransmittedCountIn   =    (mibTrigger ?
                             (mibdot1180MHzFrameTransmittedCount)
                            :((clearEvent) ?  1'h0  : mibdot1180MHzFrameTransmittedCountReg));
                                                                
assign       mibdot11160MHzFrameTransmittedCountIn   =    (mibTrigger ?
                             (mibdot11160MHzFrameTransmittedCount)
                            :((clearEvent) ?  1'h0  : mibdot11160MHzFrameTransmittedCountReg));
                                                                
assign       mibdot1120MHzFrameReceivedCountIn   =    (mibTrigger ?
                             (mibdot1120MHzFrameReceivedCount)
                            :((clearEvent) ?  1'h0  : mibdot1120MHzFrameReceivedCountReg));
                                                                
assign       mibdot1140MHzFrameReceivedCountIn   =    (mibTrigger ?
                             (mibdot1140MHzFrameReceivedCount)
                            :((clearEvent) ?  1'h0  : mibdot1140MHzFrameReceivedCountReg));
                                                                
assign       mibdot1180MHzFrameReceivedCountIn   =    (mibTrigger ?
                             (mibdot1180MHzFrameReceivedCount)
                            :((clearEvent) ?  1'h0  : mibdot1180MHzFrameReceivedCountReg));
                                                                
assign       mibdot11160MHzFrameReceivedCountIn   =    (mibTrigger ?
                             (mibdot11160MHzFrameReceivedCount)
                            :((clearEvent) ?  1'h0  : mibdot11160MHzFrameReceivedCountReg));
                                                                
assign       mibrw20MHzFailedTXOPCountIn   =    (mibTrigger ?
                             (mibrw20MHzFailedTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw20MHzFailedTXOPCountReg));
                                                                
assign       mibrw20MHzSuccessfulTXOPCountIn   =    (mibTrigger ?
                             (mibrw20MHzSuccessfulTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw20MHzSuccessfulTXOPCountReg));
                                                                
assign       mibrw40MHzFailedTXOPCountIn   =    (mibTrigger ?
                             (mibrw40MHzFailedTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw40MHzFailedTXOPCountReg));
                                                                
assign       mibrw40MHzSuccessfulTXOPCountIn   =    (mibTrigger ?
                             (mibrw40MHzSuccessfulTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw40MHzSuccessfulTXOPCountReg));
                                                                
assign       mibrw80MHzFailedTXOPCountIn   =    (mibTrigger ?
                             (mibrw80MHzFailedTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw80MHzFailedTXOPCountReg));
                                                                
assign       mibrw80MHzSuccessfulTXOPCountIn   =    (mibTrigger ?
                             (mibrw80MHzSuccessfulTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw80MHzSuccessfulTXOPCountReg));
                                                                
assign       mibrw160MHzFailedTXOPCountIn   =    (mibTrigger ?
                             (mibrw160MHzFailedTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw160MHzFailedTXOPCountReg));
                                                                
assign       mibrw160MHzSuccessfulTXOPCountIn   =    (mibTrigger ?
                             (mibrw160MHzSuccessfulTXOPCount)
                            :((clearEvent) ?  1'h0  : mibrw160MHzSuccessfulTXOPCountReg));
                                                                
assign       mibrwDynBWDropCountIn   =    (mibTrigger ?
                             (mibrwDynBWDropCount)
                            :((clearEvent) ?  1'h0  : mibrwDynBWDropCountReg));
                                                                
assign       mibrwStaBWFailedCountIn   =    (mibTrigger ?
                             (mibrwStaBWFailedCount)
                            :((clearEvent) ?  1'h0  : mibrwStaBWFailedCountReg));
                                                                
assign       mibdot11DualCTSSuccessCountIn   =    (mibTrigger ?
                             (mibdot11DualCTSSuccessCount)
                            :((clearEvent) ?  1'h0  : mibdot11DualCTSSuccessCountReg));
                                                                
assign       mibdot11STBCCTSSuccessCountIn   =    (mibTrigger ?
                             (mibdot11STBCCTSSuccessCount)
                            :((clearEvent) ?  1'h0  : mibdot11STBCCTSSuccessCountReg));
                                                                
assign       mibdot11STBCCTSFailureCountIn   =    (mibTrigger ?
                             (mibdot11STBCCTSFailureCount)
                            :((clearEvent) ?  1'h0  : mibdot11STBCCTSFailureCountReg));
                                                                
assign       mibdot11nonSTBCCTSSuccessCountIn   =    (mibTrigger ?
                             (mibdot11nonSTBCCTSSuccessCount)
                            :((clearEvent) ?  1'h0  : mibdot11nonSTBCCTSSuccessCountReg));
                                                                
assign       mibdot11nonSTBCCTSFailureCountIn   =    (mibTrigger ?
                             (mibdot11nonSTBCCTSFailureCount)
                            :((clearEvent) ?  1'h0  : mibdot11nonSTBCCTSFailureCountReg));
                                                                
                                                  
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11WEPExcludedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11WEPExcludedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11WEPExcludedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11WEPExcludedCountReg      <=      mibdot11WEPExcludedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11FCSErrorCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11FCSErrorCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11FCSErrorCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11FCSErrorCountReg      <=      mibdot11FCSErrorCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwRxPHYErrorCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwRxPHYErrorCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwRxPHYErrorCountReg      <=      1'h0;
  end
  else
  begin
    mibrwRxPHYErrorCountReg      <=      mibrwRxPHYErrorCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwRxFIFOOverflowCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwRxFIFOOverflowCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwRxFIFOOverflowCountReg      <=      1'h0;
  end
  else
  begin
    mibrwRxFIFOOverflowCountReg      <=      mibrwRxFIFOOverflowCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwTxUnderrunCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwTxUnderrunCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwTxUnderrunCountReg      <=      1'h0;
  end
  else
  begin
    mibrwTxUnderrunCountReg      <=      mibrwTxUnderrunCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwQosUTransmittedMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwQosUTransmittedMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwQosUTransmittedMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwQosUTransmittedMPDUCountReg      <=      mibrwQosUTransmittedMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwQosGTransmittedMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwQosGTransmittedMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwQosGTransmittedMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwQosGTransmittedMPDUCountReg      <=      mibrwQosGTransmittedMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11QosFailedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11QosFailedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11QosFailedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11QosFailedCountReg      <=      mibdot11QosFailedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11QosRetryCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11QosRetryCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11QosRetryCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11QosRetryCountReg      <=      mibdot11QosRetryCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11QosRTSSuccessCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11QosRTSSuccessCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11QosRTSSuccessCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11QosRTSSuccessCountReg      <=      mibdot11QosRTSSuccessCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11QosRTSFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11QosRTSFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11QosRTSFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11QosRTSFailureCountReg      <=      mibdot11QosRTSFailureCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwQosACKFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwQosACKFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwQosACKFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibrwQosACKFailureCountReg      <=      mibrwQosACKFailureCountIn;
  end
end

// Below always block imitates flop to 
 // register MIB mibrwQosUReceivedMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwQosUReceivedMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwQosUReceivedMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwQosUReceivedMPDUCountReg      <=      mibrwQosUReceivedMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwQosGReceivedMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwQosGReceivedMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwQosGReceivedMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwQosGReceivedMPDUCountReg      <=      mibrwQosGReceivedMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwQosUReceivedOtherMPDU value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwQosUReceivedOtherMPDUReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwQosUReceivedOtherMPDUReg      <=      1'h0;
  end
  else
  begin
    mibrwQosUReceivedOtherMPDUReg      <=      mibrwQosUReceivedOtherMPDUIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11QosRetriesReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11QosRetriesReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11QosRetriesReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11QosRetriesReceivedCountReg      <=      mibdot11QosRetriesReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwUTransmittedAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwUTransmittedAMSDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwUTransmittedAMSDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwUTransmittedAMSDUCountReg      <=      mibrwUTransmittedAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwGTransmittedAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwGTransmittedAMSDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwGTransmittedAMSDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwGTransmittedAMSDUCountReg      <=      mibrwGTransmittedAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11FailedAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11FailedAMSDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11FailedAMSDUCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11FailedAMSDUCountReg      <=      mibdot11FailedAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11RetryAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11RetryAMSDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11RetryAMSDUCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11RetryAMSDUCountReg      <=      mibdot11RetryAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11TransmittedOctetsInAMSDU value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11TransmittedOctetsInAMSDUReg      <=      16'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11TransmittedOctetsInAMSDUReg      <=      16'h0;
  end
  else
  begin
    mibdot11TransmittedOctetsInAMSDUReg      <=      mibdot11TransmittedOctetsInAMSDUIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11AMSDUAckFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11AMSDUAckFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11AMSDUAckFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11AMSDUAckFailureCountReg      <=      mibdot11AMSDUAckFailureCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwUReceivedAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwUReceivedAMSDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwUReceivedAMSDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwUReceivedAMSDUCountReg      <=      mibrwUReceivedAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwGReceivedAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwGReceivedAMSDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwGReceivedAMSDUCountReg      <=      1'h0;
  end
  else
  begin
    mibrwGReceivedAMSDUCountReg      <=      mibrwGReceivedAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwUReceivedOtherAMSDU value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwUReceivedOtherAMSDUReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwUReceivedOtherAMSDUReg      <=      1'h0;
  end
  else
  begin
    mibrwUReceivedOtherAMSDUReg      <=      mibrwUReceivedOtherAMSDUIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11ReceivedOctetsInAMSDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11ReceivedOctetsInAMSDUCountReg      <=      16'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11ReceivedOctetsInAMSDUCountReg      <=      16'h0;
  end
  else
  begin
    mibdot11ReceivedOctetsInAMSDUCountReg      <=      mibdot11ReceivedOctetsInAMSDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11TransmittedAMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11TransmittedAMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11TransmittedAMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11TransmittedAMPDUCountReg      <=      mibdot11TransmittedAMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11TransmittedMPDUInAMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11TransmittedMPDUInAMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11TransmittedMPDUInAMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11TransmittedMPDUInAMPDUCountReg      <=      mibdot11TransmittedMPDUInAMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11TransmittedOctetsInAMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11TransmittedOctetsInAMPDUCountReg      <=      16'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11TransmittedOctetsInAMPDUCountReg      <=      16'h0;
  end
  else
  begin
    mibdot11TransmittedOctetsInAMPDUCountReg      <=      mibdot11TransmittedOctetsInAMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwUAMPDUReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwUAMPDUReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwUAMPDUReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibrwUAMPDUReceivedCountReg      <=      mibrwUAMPDUReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwGAMPDUReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwGAMPDUReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwGAMPDUReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibrwGAMPDUReceivedCountReg      <=      mibrwGAMPDUReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwOtherAMPDUReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwOtherAMPDUReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwOtherAMPDUReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibrwOtherAMPDUReceivedCountReg      <=      mibrwOtherAMPDUReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11MPDUInReceivedAMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11MPDUInReceivedAMPDUCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11MPDUInReceivedAMPDUCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11MPDUInReceivedAMPDUCountReg      <=      mibdot11MPDUInReceivedAMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11ReceivedOctetsInAMPDUCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11ReceivedOctetsInAMPDUCountReg      <=      16'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11ReceivedOctetsInAMPDUCountReg      <=      16'h0;
  end
  else
  begin
    mibdot11ReceivedOctetsInAMPDUCountReg      <=      mibdot11ReceivedOctetsInAMPDUCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11AMPDUDelimiterCRCErrorCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11AMPDUDelimiterCRCErrorCountReg      <=      8'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11AMPDUDelimiterCRCErrorCountReg      <=      8'h0;
  end
  else
  begin
    mibdot11AMPDUDelimiterCRCErrorCountReg      <=      mibdot11AMPDUDelimiterCRCErrorCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11ImplicitBARFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11ImplicitBARFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11ImplicitBARFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11ImplicitBARFailureCountReg      <=      mibdot11ImplicitBARFailureCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11ExplicitBARFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11ExplicitBARFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11ExplicitBARFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11ExplicitBARFailureCountReg      <=      mibdot11ExplicitBARFailureCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot1120MHzFrameTransmittedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot1120MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot1120MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot1120MHzFrameTransmittedCountReg      <=      mibdot1120MHzFrameTransmittedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot1140MHzFrameTransmittedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot1140MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot1140MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot1140MHzFrameTransmittedCountReg      <=      mibdot1140MHzFrameTransmittedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot1180MHzFrameTransmittedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot1180MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot1180MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot1180MHzFrameTransmittedCountReg      <=      mibdot1180MHzFrameTransmittedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11160MHzFrameTransmittedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11160MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11160MHzFrameTransmittedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11160MHzFrameTransmittedCountReg      <=      mibdot11160MHzFrameTransmittedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot1120MHzFrameReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot1120MHzFrameReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot1120MHzFrameReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot1120MHzFrameReceivedCountReg      <=      mibdot1120MHzFrameReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot1140MHzFrameReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot1140MHzFrameReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot1140MHzFrameReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot1140MHzFrameReceivedCountReg      <=      mibdot1140MHzFrameReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot1180MHzFrameReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot1180MHzFrameReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot1180MHzFrameReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot1180MHzFrameReceivedCountReg      <=      mibdot1180MHzFrameReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11160MHzFrameReceivedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11160MHzFrameReceivedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11160MHzFrameReceivedCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11160MHzFrameReceivedCountReg      <=      mibdot11160MHzFrameReceivedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw20MHzFailedTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw20MHzFailedTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw20MHzFailedTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw20MHzFailedTXOPCountReg      <=      mibrw20MHzFailedTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw20MHzSuccessfulTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw20MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw20MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw20MHzSuccessfulTXOPCountReg      <=      mibrw20MHzSuccessfulTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw40MHzFailedTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw40MHzFailedTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw40MHzFailedTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw40MHzFailedTXOPCountReg      <=      mibrw40MHzFailedTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw40MHzSuccessfulTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw40MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw40MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw40MHzSuccessfulTXOPCountReg      <=      mibrw40MHzSuccessfulTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw80MHzFailedTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw80MHzFailedTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw80MHzFailedTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw80MHzFailedTXOPCountReg      <=      mibrw80MHzFailedTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw80MHzSuccessfulTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw80MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw80MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw80MHzSuccessfulTXOPCountReg      <=      mibrw80MHzSuccessfulTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw160MHzFailedTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw160MHzFailedTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw160MHzFailedTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw160MHzFailedTXOPCountReg      <=      mibrw160MHzFailedTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrw160MHzSuccessfulTXOPCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrw160MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrw160MHzSuccessfulTXOPCountReg      <=      1'h0;
  end
  else
  begin
    mibrw160MHzSuccessfulTXOPCountReg      <=      mibrw160MHzSuccessfulTXOPCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwDynBWDropCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwDynBWDropCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwDynBWDropCountReg      <=      1'h0;
  end
  else
  begin
    mibrwDynBWDropCountReg      <=      mibrwDynBWDropCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibrwStaBWFailedCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibrwStaBWFailedCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibrwStaBWFailedCountReg      <=      1'h0;
  end
  else
  begin
    mibrwStaBWFailedCountReg      <=      mibrwStaBWFailedCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11DualCTSSuccessCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11DualCTSSuccessCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11DualCTSSuccessCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11DualCTSSuccessCountReg      <=      mibdot11DualCTSSuccessCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11STBCCTSSuccessCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11STBCCTSSuccessCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11STBCCTSSuccessCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11STBCCTSSuccessCountReg      <=      mibdot11STBCCTSSuccessCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11STBCCTSFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11STBCCTSFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11STBCCTSFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11STBCCTSFailureCountReg      <=      mibdot11STBCCTSFailureCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11nonSTBCCTSSuccessCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11nonSTBCCTSSuccessCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11nonSTBCCTSSuccessCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11nonSTBCCTSSuccessCountReg      <=      mibdot11nonSTBCCTSSuccessCountIn;
  end
end
                                       
 // Below always block imitates flop to 
 // register MIB mibdot11nonSTBCCTSFailureCount value exposed during mibTrigger
                                       
always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(macCoreClkHardRst_n == 1'b0)
  begin
    mibdot11nonSTBCCTSFailureCountReg      <=      1'h0;
  end
  else if(macCoreClkSoftRst_n == 1'b0)
  begin
    mibdot11nonSTBCCTSFailureCountReg      <=      1'h0;
  end
  else
  begin
    mibdot11nonSTBCCTSFailureCountReg      <=      mibdot11nonSTBCCTSFailureCountIn;
  end
end
                                                  
                                                  
                                                  
                                                  
   
   
   // mibTIDIndex latching.
   
   // TIDIndex exposed at the mib_MAC Controller shall also be
   // latched in this module similar to mibs latched.
   // clearing of the tidIndex shall also take place on
   // clearEvent indication from accessArbiter which shall
   // initiate reset of the MIB table in RAM by writting zero
   // at every location
   assign tidIndexIn = (mibTrigger && !mibHWUpdateStart) ? mibTIDIndex : (clearEvent) ? 3'b0 : tidIndexReg;

   
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin

        // condition : macCoreClkHardRst_n
        // source    : power On Reset (active low)
        // set       : its active low signal. set on power
        //             reset
        // result    : resets the flop
        if(macCoreClkHardRst_n == 1'b0)
          begin
             tidIndexReg <= 3'b0;
          end

        // condition : macCoreClkSoftRst_n
        // source    : soft or synchronous reset
        // set       : its active high signal. set by
        //             Software
        // result    : resets the flop
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             tidIndexReg <= 3'b0;
          end
        else
          begin
             tidIndexReg <= tidIndexIn;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)


   
   // Always block to flop the mib Trigger
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin

        // condition : macCoreClkHardRst_n
        // source    : power On Reset (active low)
        // set       : its active low signal. set on power
        //             reset
        // result    : resets the flop
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibTriggerD <= 1'b0;
          end

        // condition : macCoreClkSoftRst_n
        // source    : soft or synchronous reset
        // set       : its active high signal. set by
        //             Software
        // result    : resets the flop
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibTriggerD <= 1'b0;
          end
        else
          begin
             mibTriggerD <= mibTrigger;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)


   // Always block to flop the mib Trigger
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin

        // condition : macCoreClkHardRst_n
        // source    : power On Reset (active low)
        // set       : its active low signal. set on power
        //             reset
        // result    : resets the flop
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibTriggerDD <= 1'b0;
          end

        // condition : macCoreClkSoftRst_n
        // source    : soft or synchronous reset
        // set       : its active high signal. set by
        //             Software
        // result    : resets the flop
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibTriggerDD <= 1'b0;
          end
        else
          begin
             mibTriggerDD <= mibTriggerD;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)
   
   /////////////////////////////END OF Field register Logic/////////////////////////////////

   
   // b) Event Detector Logic:
   
   // Event Detector module shall find out the active mib out of the
   // all mib latched during the mib trigger.
   // All MIB latched shall be converted into single bit representation
   // which shall be indicating that whether particular MIB is active
   // or not. That is done by ORing all bits of particular MIB and
   // its non zero status shall be indicating active MIB
   
assign  mibReg   = {
                            mibdot11nonSTBCCTSFailureCountReg,
                            mibdot11nonSTBCCTSSuccessCountReg,
                            mibdot11STBCCTSFailureCountReg,
                            mibdot11STBCCTSSuccessCountReg,
                            mibdot11DualCTSSuccessCountReg,
                            mibrwStaBWFailedCountReg,
                            mibrwDynBWDropCountReg,
                            mibrw160MHzSuccessfulTXOPCountReg,
                            mibrw160MHzFailedTXOPCountReg,
                            mibrw80MHzSuccessfulTXOPCountReg,
                            mibrw80MHzFailedTXOPCountReg,
                            mibrw40MHzSuccessfulTXOPCountReg,
                            mibrw40MHzFailedTXOPCountReg,
                            mibrw20MHzSuccessfulTXOPCountReg,
                            mibrw20MHzFailedTXOPCountReg,
                            mibdot11160MHzFrameReceivedCountReg,
                            mibdot1180MHzFrameReceivedCountReg,
                            mibdot1140MHzFrameReceivedCountReg,
                            mibdot1120MHzFrameReceivedCountReg,
                            mibdot11160MHzFrameTransmittedCountReg,
                            mibdot1180MHzFrameTransmittedCountReg,
                            mibdot1140MHzFrameTransmittedCountReg,
                            mibdot1120MHzFrameTransmittedCountReg,
                            mibdot11ExplicitBARFailureCountReg,
                            mibdot11ImplicitBARFailureCountReg,
                            |mibdot11AMPDUDelimiterCRCErrorCountReg,
                            |mibdot11ReceivedOctetsInAMPDUCountReg,
                            mibdot11MPDUInReceivedAMPDUCountReg,
                            mibrwOtherAMPDUReceivedCountReg,
                            mibrwGAMPDUReceivedCountReg,
                            mibrwUAMPDUReceivedCountReg,
                            |mibdot11TransmittedOctetsInAMPDUCountReg,
                            mibdot11TransmittedMPDUInAMPDUCountReg,
                            mibdot11TransmittedAMPDUCountReg,
                            |mibdot11ReceivedOctetsInAMSDUCountReg,
                            mibrwUReceivedOtherAMSDUReg,
                            mibrwGReceivedAMSDUCountReg,
                            mibrwUReceivedAMSDUCountReg,
                            mibdot11AMSDUAckFailureCountReg,
                            |mibdot11TransmittedOctetsInAMSDUReg,
                            mibdot11RetryAMSDUCountReg,
                            mibdot11FailedAMSDUCountReg,
                            mibrwGTransmittedAMSDUCountReg,
                            mibrwUTransmittedAMSDUCountReg,
                            mibdot11QosRetriesReceivedCountReg,
                            mibrwQosUReceivedOtherMPDUReg,
                            mibrwQosGReceivedMPDUCountReg,
                            mibrwQosUReceivedMPDUCountReg,
                            mibrwQosACKFailureCountReg,
                            mibdot11QosRTSFailureCountReg,
                            mibdot11QosRTSSuccessCountReg,
                            mibdot11QosRetryCountReg,
                            mibdot11QosFailedCountReg,
                            mibrwQosGTransmittedMPDUCountReg,
                            mibrwQosUTransmittedMPDUCountReg,
                            mibrwTxUnderrunCountReg,
                            mibrwRxFIFOOverflowCountReg,
                            mibrwRxPHYErrorCountReg,
                            mibdot11FCSErrorCountReg,
                             mibdot11WEPExcludedCountReg};
   
   
   // Below sequential logic obtains the next active mib which
   // needs to be updated in the RAM.

   
   // a) Determination of first active mib Index:
   //    First Active mib Address is obtained during mib Trigger.
   //    During the mibTrigger, below always block shall search the
   //    active mib in window. With every search the bits in that 
   //    window shall be shifted so as to exclude already found MIB
   //    from next search.
   // b) Determination of the successive active mib Index:
   //    Once current MIB is passed on to the accessArbiter,
   //    flag called mibCurrAddrOutSearchNext shall be set high
   //    indicating that currently MIB is being updated and by that
   //    below logic shall find the next active MIB from window and
   //    shall keep ready the index of the next MIB to update.
   //    Now as soon as indication for completion of status update
   //    for current MIB is obtained, index for next active MIB shall
   //    be forwarded which shall inturn forward address of the next
   //    active MIB to accessArbiter
   // c) Reset Table Indication: In case of reset table indication
   //    from MAC by setting of resetTable bit in macCntrlReg1 then
   //    search and forwarding of the RAM address for active RAM shall
   //    be stopped and fields shall be cleared
   //    

   ////////////////////////////////////////////////////////////////////////
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        // Power On Reset. Initialize all the
       // flops to thier initiale values
        if(macCoreClkHardRst_n == 1'b0)
          begin
             shiftMibFieldReg    <= `TotalMIBDefined'd0;
             mibIndexCurrent     <= `RW_MIB_INDEX_WIDTH'd0;
             mibIndexNext        <= `RW_MIB_INDEX_WIDTH'd0;
             windowShiftCnt      <= `ShiftWindowCnt'd0;
             mibHWUpdateStart    <= 1'b0;
          end

        // Soft Reset or Synchronous Reset made
        // by software. It initializes flop
        // to their initial values
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             shiftMibFieldReg    <= `TotalMIBDefined'd0;
             mibIndexCurrent     <= `RW_MIB_INDEX_WIDTH'd0;
             mibIndexNext        <= `RW_MIB_INDEX_WIDTH'd0;
             windowShiftCnt      <= `ShiftWindowCnt'd0;
             mibHWUpdateStart    <= 1'b0;
          end

        // Indication from accessArbiter which
        // shall indicate that MIB table in RAM
        // needs to be reset to zero and
        // for that all the bits in shift register
        // shall be written with 1 and after every
        // update next address of the ram shall
        // be passed to accessArbiter where accessArbiter
        // shall write 0000 at that location
        else if(mibTableResetTable || clearEvent)
          begin
             shiftMibFieldReg    <= `TotalMIBDefined'd0;
             mibHWUpdateStart    <= 1'b0;
             mibIndexCurrent     <= `RW_MIB_INDEX_WIDTH'd0;
             mibIndexNext        <= `RW_MIB_INDEX_WIDTH'd0;
             mibHWUpdateStart    <= 1'b0;
          end

        // condition : mibTrigger
        // source    : MAC Controller
        // set       : when set to one, indicates that
        //             new set of MIBs needs to be 
        //             updated in RAM.
        // Result    : indicates that new set of MIB needs
        //             to be updated in RAM and for which
        //             search for active MIB needs to began by 
        //             loading the shift register with mibReg
        //             and resetting all flags
        //
        else if(mibTriggerDD && !mibHWUpdateStart)
          begin
             shiftMibFieldReg       <= mibReg;
             mibIndexCurrent        <= `RW_MIB_INDEX_WIDTH'd0;
             mibIndexNext           <= `RW_MIB_INDEX_WIDTH'd0;
             
             windowShiftCnt         <= `ShiftWindowCnt'd0;
             mibHWUpdateStart       <= 1'b0;
          end 

        // condition : shiftMibFieldReg
        // source    : mibReg
        // Set       : Its shift register
        //             loaded with bit representaion
        //             of the MIBs
        // Result    : if all bits in shift register
        //             is zero then in that case,HW update
        //             shall be stopped asserting flag mibHWUpdated
        else if(!(|shiftMibFieldReg))
          begin
             mibHWUpdateStart       <= 1'b0;
             mibIndexCurrent        <= mibIndexCurrent;
             mibIndexNext           <= `RW_MIB_INDEX_WIDTH'd0;
          end

        // condition : shiftMibWindow
        // source    : combi-block which obtains the 
        //             Index of the active MIB from 
        //             MIB window.
        // Set       : It is set to one when, all the MIBs
        //             in window are non active and new window
        //             needs to be loaded ( which occurs by
        //             shifting the shift register)
        // Result    : If this condition is met then shift
        //             register shall be shifted in order to
        //             load the window by new sets of MIBs to
        //             look for active MIBs. At same time
        //             count of the shift shall also be incremented
        //             so as to keep track by how much index needs to
        //             be incremented.
        else if(~(|(shiftMibFieldReg[`RW_MIB_WINDOW_SIZE-1 :0])))
          begin
             shiftMibFieldReg    <= shiftMibFieldReg >> `TotalMIBDefined'd`RW_MIB_WINDOW_SIZE;
             windowShiftCnt      <= windowShiftCnt + `ShiftWindowCnt'd1;
             mibIndexNext        <= `RW_MIB_INDEX_WIDTH'd0;
             mibHWUpdateStart    <= 1'b0; 
          end

        // condition: ramUpdated 
        // source   : memoryController
        // set      : indicates that current active MIB has 
        //            been updated and can now go for update
        //            of other active MIB in row.
        // Result   : During ramUpdated indication, dataLatch can
        //            pass on the next memory address of active
        //            MIB in row. Index of same shall be obtained 
        //            as given in RTL. At same time, search for
        //            next active MIB can also began.
        // 
        else if(ramUpdated)
          begin
             
             // When ramUpdated is received for  update
             // of Current active MIB in RAM and if by
             // that time window has been shifted then,
             // index for next active MIB is obtained
             // directly and mibIndexNext shall be having
             // zero value
             if(shiftMibWindowReg)
               begin
                  if(|windowShiftCnt)
                    begin
                       mibIndexCurrent                 <= ((`RW_MIB_INDEX_WIDTH'd`RW_MIB_WINDOW_SIZE * {ZERO_CT[`RW_MIB_INDEX_WIDTH - `ShiftWindowCnt - 1:0] ,windowShiftCnt}) + {ZERO_CT[`RW_MIB_INDEX_WIDTH - `RW_MIB_WINDOW_WIDTH - 1:0] ,nextMibIndexCurrent});
                    end
               end // if (shiftMibWindowReg)
             else
               begin          
                  mibIndexCurrent                     <= mibIndexNext;
               end // else: !if(shiftMibWindowReg)
             shiftMibFieldReg[nextMibIndexCurrent - `RW_MIB_WINDOW_WIDTH'd1] <= 1'b0;
             mibHWUpdateStart                                        <= 1'b1;
          end // if (ramUpdated)

        // condition : mibCurrAddOutSearchNext
        // source    : Flop
        // set       : this flag shall be set to
        //             one if index for active
        //             MIB points towards fresh
        //             value. And reset to zero
        //             on ramUpdated indication
        //             or mibTrigger
        // Result   : Indicates that cuurently update for
        //            active MIB is under way hence queue
        //            index of next active MIB to mibIndexNext
        else if (mibCurrAddrOutSearchNext)
          begin
             if(|windowShiftCnt)
               begin
                  mibIndexNext   <= ((`RW_MIB_INDEX_WIDTH'd`RW_MIB_WINDOW_SIZE * {ZERO_CT[`RW_MIB_INDEX_WIDTH - `ShiftWindowCnt - 1:0] ,windowShiftCnt}) + {ZERO_CT[`RW_MIB_INDEX_WIDTH - `RW_MIB_WINDOW_WIDTH - 1:0] ,nextMibIndexCurrent});
               end
             else
               begin
                  mibIndexNext   <= {ZERO_CT[`RW_MIB_INDEX_WIDTH - `RW_MIB_WINDOW_WIDTH - 1:0] ,nextMibIndexCurrent};
               end
             mibHWUpdateStart    <= 1'b1;
          end // if (mibCurrAddrOutSearchNext)

        // condition : When all of the above
        //             condition are not met.
        // source    : -
        // set       : -
        // Result    : In absence of all the above 
        //             conditions, shall be indicating
        //             that active MIB is being searched
        //             and index obtained shall be loaded
        //             to mibIndexCurrent and search for
        //             new index shall begin
        else if((mibIndexCurrent == `RW_MIB_INDEX_WIDTH'd0)  || shiftMibWindowReg)
          begin
             if(|windowShiftCnt)
               begin
                  mibIndexCurrent                 <= ((`RW_MIB_INDEX_WIDTH'd`RW_MIB_WINDOW_SIZE * {ZERO_CT[`RW_MIB_INDEX_WIDTH - `ShiftWindowCnt - 1:0] ,windowShiftCnt}) + {ZERO_CT[`RW_MIB_INDEX_WIDTH - `RW_MIB_WINDOW_WIDTH - 1:0] ,nextMibIndexCurrent});
               end
             else
               begin
                  mibIndexCurrent                 <= {ZERO_CT[`RW_MIB_INDEX_WIDTH - `RW_MIB_WINDOW_WIDTH - 1:0] ,nextMibIndexCurrent};
               end
          
             shiftMibFieldReg[nextMibIndexCurrent - `RW_MIB_WINDOW_WIDTH'd1]  <= 1'b0;
             mibHWUpdateStart                                         <= 1'b1;
          end // else: !if(mibIndexCurrFWFlag)
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)

        
       
                 
                  
   /**********************************************************************/
   // Always block used to search active MIB from the
   // window of the MIB
   // As soon as new values are loaded in the shift register
   // this always block shall be executed which shall update
   // index of active MIB by next MIB which needs to be
   // updated
   

   
   always@(shiftMibFieldReg)
     begin
        nextMibIndexCurrent  = {`RW_MIB_WINDOW_WIDTH{1'b0}};
        incCounter           = {`RW_MIB_WINDOW_WIDTH{1'b0}};
        shiftMibWindow       = 1'b0;
        
        if(|shiftMibFieldReg[`RW_MIB_WINDOW_SIZE-1 :0])
          begin
             for(i=0;i<=`RW_MIB_WINDOW_SIZE-1;i=i+1)
               begin
                  if(shiftMibFieldReg[i])
                    begin
                       // nextMibIndexCurrent shall be incremented
                       // with every Active MIB in window.
                       // Hence at end of the for loop count
                       // nextMibIndexCurrent shall be pointing
                       // towards last MIB active in window
                       nextMibIndexCurrent = incCounter + `RW_MIB_WINDOW_WIDTH'd1;
                       incCounter          = incCounter + `RW_MIB_WINDOW_WIDTH'd1;
                    end
                  else
                    // till active mib is found, incCounter should
                    // be incremented to count positions of MIB
                    // which have been already looked for active
                    // MIB
                    begin
                       incCounter       = incCounter + `RW_MIB_WINDOW_WIDTH'd1;
                    end
               end // for (i = 0; i <=RW_MIB_WINDOW_SIZE; i = i+1)
          end // if (|shiftMibFieldReg[`RW_MIB_WINDOW_SIZE-1 :0])
        
        // if no MIB in window is active then shiftMibWindow
        // flag is set to one and window is shifted.
        else
          begin
             shiftMibWindow = 1'b1;
          end // else: !if(|shiftMibFieldReg[`RW_MIB_WINDOW_SIZE-1 :0])
     end // always@ (shiftMibFieldReg)

   
   
   // always block that shall indcate that current count of the active
   // MIB index has been forwarded to event research engine and know
   // event research engine can look for other active MIB.
   // Flag mibCurrentAddrOutSearchNext shall be set to one
   // when Index pointing towards current active MIB is new
   // and same flag shall be reset to zero when either
   // mibTrigger happens or ramUpdated indication from
   // memoryController
   // This flag shall be used to calculate the next active MIB
   // when current active MIB is being updated in the ram
   // 
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibCurrAddrOutSearchNext <= 1'b0;
          end

        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibCurrAddrOutSearchNext <= 1'b0;
          end
        
        // condition : mibTrigger OR ramUpdated
        // source    : mibTrigger --- MAC Controller
        //             ramUpdated --- memoryController
        // set       : mibTrigger --- when new set of MIB
        //                            needs to be updated
        //             ramUpdated --- when update of current
        //                            MIB is done
        // result    : resets the flag mibCurrentAddrOutSearchNext
        else if((mibTriggerDD && !mibHWUpdateStart) || (~(|(shiftMibFieldReg[`RW_MIB_WINDOW_SIZE-1 :0])) 
                                 && ramUpdated))
          begin
             mibCurrAddrOutSearchNext <= 1'b0;
          end

        // condition : mibIndexCurrent != mibIndexCurrentFF
        //             when mibIdexCurrent has fresh value
        //             active MIB
        // source    : Always block used to calculate MIB
        //             Index
        // set       : -
        // result    : when mib Index is updated
        //             with new value then flag needs to
        //             be set high
        else if((mibIndexCurrent != mibIndexCurrentFF ))
                //&& !shiftMibWindow)
          begin
             mibCurrAddrOutSearchNext <= 1'b1;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)
   

   // Registering the signal shiftMibWindow
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          begin
             shiftMibWindowReg <= 1'b0;
          end
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             shiftMibWindowReg <= 1'b0;
          end
        else
          begin
             shiftMibWindowReg <= shiftMibWindow;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)
   
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibIndexCurrentFF <= `RW_MIB_INDEX_WIDTH'd0;
          end
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibIndexCurrentFF <= `RW_MIB_INDEX_WIDTH'd0;
          end
        else
          begin
             mibIndexCurrentFF <= mibIndexCurrent;
          end
     end // always@ (posedge macCoreClk or negedge macCoreClkHardRst_n)
   
               
   ////////////////////////////////////////////////////////////////////////
   
  // Registering the mibIncrementCnt
   always@(posedge macCoreClk or negedge macCoreClkHardRst_n)
     begin
        if(macCoreClkHardRst_n == 1'b0)
          begin
             mibIncrementCnt <= `IncWidth'd0;
          end
        else if(macCoreClkSoftRst_n == 1'b0)
          begin
             mibIncrementCnt <= `IncWidth'd0;
          end
        else
          begin
             mibIncrementCnt <= mibIncrementCntRaw;
          end
     end
   
                                          
                                          
                                          
                                          
// c) Event Research Engine:
                            
// Event Research Engine shall provide
// the ram address fo the active mib to
// the Access Arbiter.                 
// event research engine is mux from   
// where address corresponding to active
// mib index obtained from event detector
// is searched.                          
                                         
assign mibAddrOut = (mibAddrOutRawInt + {5'b00,tidIndexInt});
                                             
                                             
                                             
always@(mibIndexCurrent or tidIndexReg)      
     begin                                   
       case(mibIndexCurrent)                 
                                             
                                             
                                             
          10'd1:
             begin
                mibAddrOutRawInt = ADDRESSMIB1_CT;
              tidIndexInt      = 3'b0;
             end

          10'd2:
             begin
                mibAddrOutRawInt = ADDRESSMIB2_CT;
              tidIndexInt      = 3'b0;
             end

          10'd3:
             begin
                mibAddrOutRawInt = ADDRESSMIB3_CT;
              tidIndexInt      = 3'b0;
             end

          10'd4:
             begin
                mibAddrOutRawInt = ADDRESSMIB4_CT;
              tidIndexInt      = 3'b0;
             end

          10'd5:
             begin
                mibAddrOutRawInt = ADDRESSMIB5_CT;
              tidIndexInt      = 3'b0;
             end

          10'd6:
             begin
                mibAddrOutRawInt = ADDRESSMIB6_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd7:
             begin
                mibAddrOutRawInt = ADDRESSMIB7_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd8:
             begin
                mibAddrOutRawInt = ADDRESSMIB8_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd9:
             begin
                mibAddrOutRawInt = ADDRESSMIB9_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd10:
             begin
                mibAddrOutRawInt = ADDRESSMIB10_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd11:
             begin
                mibAddrOutRawInt = ADDRESSMIB11_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd12:
             begin
                mibAddrOutRawInt = ADDRESSMIB12_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd13:
             begin
                mibAddrOutRawInt = ADDRESSMIB13_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd14:
             begin
                mibAddrOutRawInt = ADDRESSMIB14_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd15:
             begin
                mibAddrOutRawInt = ADDRESSMIB15_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd16:
             begin
                mibAddrOutRawInt = ADDRESSMIB16_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd17:
             begin
                mibAddrOutRawInt = ADDRESSMIB17_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd18:
             begin
                mibAddrOutRawInt = ADDRESSMIB18_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd19:
             begin
                mibAddrOutRawInt = ADDRESSMIB19_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd20:
             begin
                mibAddrOutRawInt = ADDRESSMIB20_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd21:
             begin
                mibAddrOutRawInt = ADDRESSMIB21_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd22:
             begin
                mibAddrOutRawInt = ADDRESSMIB22_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd23:
             begin
                mibAddrOutRawInt = ADDRESSMIB23_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd24:
             begin
                mibAddrOutRawInt = ADDRESSMIB24_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd25:
             begin
                mibAddrOutRawInt = ADDRESSMIB25_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd26:
             begin
                mibAddrOutRawInt = ADDRESSMIB26_CT;
              tidIndexInt      = tidIndexReg;
             end

          10'd27:
             begin
                mibAddrOutRawInt = ADDRESSMIB27_CT;
              tidIndexInt      = 3'b0;
             end

          10'd28:
             begin
                mibAddrOutRawInt = ADDRESSMIB28_CT;
              tidIndexInt      = 3'b0;
             end

          10'd29:
             begin
                mibAddrOutRawInt = ADDRESSMIB29_CT;
              tidIndexInt      = 3'b0;
             end

          10'd30:
             begin
                mibAddrOutRawInt = ADDRESSMIB30_CT;
              tidIndexInt      = 3'b0;
             end

          10'd31:
             begin
                mibAddrOutRawInt = ADDRESSMIB31_CT;
              tidIndexInt      = 3'b0;
             end

          10'd32:
             begin
                mibAddrOutRawInt = ADDRESSMIB32_CT;
              tidIndexInt      = 3'b0;
             end

          10'd33:
             begin
                mibAddrOutRawInt = ADDRESSMIB33_CT;
              tidIndexInt      = 3'b0;
             end

          10'd34:
             begin
                mibAddrOutRawInt = ADDRESSMIB34_CT;
              tidIndexInt      = 3'b0;
             end

          10'd35:
             begin
                mibAddrOutRawInt = ADDRESSMIB35_CT;
              tidIndexInt      = 3'b0;
             end

          10'd36:
             begin
                mibAddrOutRawInt = ADDRESSMIB36_CT;
              tidIndexInt      = 3'b0;
             end

          10'd37:
             begin
                mibAddrOutRawInt = ADDRESSMIB37_CT;
              tidIndexInt      = 3'b0;
             end

          10'd38:
             begin
                mibAddrOutRawInt = ADDRESSMIB38_CT;
              tidIndexInt      = 3'b0;
             end

          10'd39:
             begin
                mibAddrOutRawInt = ADDRESSMIB39_CT;
              tidIndexInt      = 3'b0;
             end

          10'd40:
             begin
                mibAddrOutRawInt = ADDRESSMIB40_CT;
              tidIndexInt      = 3'b0;
             end

          10'd41:
             begin
                mibAddrOutRawInt = ADDRESSMIB41_CT;
              tidIndexInt      = 3'b0;
             end

          10'd42:
             begin
                mibAddrOutRawInt = ADDRESSMIB42_CT;
              tidIndexInt      = 3'b0;
             end

          10'd43:
             begin
                mibAddrOutRawInt = ADDRESSMIB43_CT;
              tidIndexInt      = 3'b0;
             end

          10'd44:
             begin
                mibAddrOutRawInt = ADDRESSMIB44_CT;
              tidIndexInt      = 3'b0;
             end

          10'd45:
             begin
                mibAddrOutRawInt = ADDRESSMIB45_CT;
              tidIndexInt      = 3'b0;
             end

          10'd46:
             begin
                mibAddrOutRawInt = ADDRESSMIB46_CT;
              tidIndexInt      = 3'b0;
             end

          10'd47:
             begin
                mibAddrOutRawInt = ADDRESSMIB47_CT;
              tidIndexInt      = 3'b0;
             end

          10'd48:
             begin
                mibAddrOutRawInt = ADDRESSMIB48_CT;
              tidIndexInt      = 3'b0;
             end

          10'd49:
             begin
                mibAddrOutRawInt = ADDRESSMIB49_CT;
              tidIndexInt      = 3'b0;
             end

          10'd50:
             begin
                mibAddrOutRawInt = ADDRESSMIB50_CT;
              tidIndexInt      = 3'b0;
             end

          10'd51:
             begin
                mibAddrOutRawInt = ADDRESSMIB51_CT;
              tidIndexInt      = 3'b0;
             end

          10'd52:
             begin
                mibAddrOutRawInt = ADDRESSMIB52_CT;
              tidIndexInt      = 3'b0;
             end

          10'd53:
             begin
                mibAddrOutRawInt = ADDRESSMIB53_CT;
              tidIndexInt      = 3'b0;
             end

          10'd54:
             begin
                mibAddrOutRawInt = ADDRESSMIB54_CT;
              tidIndexInt      = 3'b0;
             end

          10'd55:
             begin
                mibAddrOutRawInt = ADDRESSMIB55_CT;
              tidIndexInt      = 3'b0;
             end

          10'd56:
             begin
                mibAddrOutRawInt = ADDRESSMIB56_CT;
              tidIndexInt      = 3'b0;
             end

          10'd57:
             begin
                mibAddrOutRawInt = ADDRESSMIB57_CT;
              tidIndexInt      = 3'b0;
             end

          10'd58:
             begin
                mibAddrOutRawInt = ADDRESSMIB58_CT;
              tidIndexInt      = 3'b0;
             end

          10'd59:
             begin
                mibAddrOutRawInt = ADDRESSMIB59_CT;
              tidIndexInt      = 3'b0;
             end

          10'd60:
             begin
                mibAddrOutRawInt = ADDRESSMIB60_CT;
              tidIndexInt      = 3'b0;
             end

   default:
     begin 
       mibAddrOutRawInt = `RW_MIB_ADDR_WIDTH'd0;
       tidIndexInt      = 3'd0;
     end 
   endcase
 end
                                              
                                              
                                              
                                              
   // always block to determine the increment
   // count by which current active mib needs
   // to be updated. mibIncrementCnt shall
   // be detected on the basis of the count
   // value or index value obtained during
   // event detector logic
   always@(
          mibdot11WEPExcludedCountReg
       or mibdot11FCSErrorCountReg
       or mibrwRxPHYErrorCountReg
       or mibrwRxFIFOOverflowCountReg
       or mibrwTxUnderrunCountReg
       or mibrwQosUTransmittedMPDUCountReg
       or mibrwQosGTransmittedMPDUCountReg
       or mibdot11QosFailedCountReg
       or mibdot11QosRetryCountReg
       or mibdot11QosRTSSuccessCountReg
       or mibdot11QosRTSFailureCountReg
       or mibrwQosACKFailureCountReg
       or mibrwQosUReceivedMPDUCountReg
       or mibrwQosGReceivedMPDUCountReg
       or mibrwQosUReceivedOtherMPDUReg
       or mibdot11QosRetriesReceivedCountReg
       or mibrwUTransmittedAMSDUCountReg
       or mibrwGTransmittedAMSDUCountReg
       or mibdot11FailedAMSDUCountReg
       or mibdot11RetryAMSDUCountReg
       or mibdot11TransmittedOctetsInAMSDUReg
       or mibdot11AMSDUAckFailureCountReg
       or mibrwUReceivedAMSDUCountReg
       or mibrwGReceivedAMSDUCountReg
       or mibrwUReceivedOtherAMSDUReg
       or mibdot11ReceivedOctetsInAMSDUCountReg
       or mibdot11TransmittedAMPDUCountReg
       or mibdot11TransmittedMPDUInAMPDUCountReg
       or mibdot11TransmittedOctetsInAMPDUCountReg
       or mibrwUAMPDUReceivedCountReg
       or mibrwGAMPDUReceivedCountReg
       or mibrwOtherAMPDUReceivedCountReg
       or mibdot11MPDUInReceivedAMPDUCountReg
       or mibdot11ReceivedOctetsInAMPDUCountReg
       or mibdot11AMPDUDelimiterCRCErrorCountReg
       or mibdot11ImplicitBARFailureCountReg
       or mibdot11ExplicitBARFailureCountReg
       or mibdot1120MHzFrameTransmittedCountReg
       or mibdot1140MHzFrameTransmittedCountReg
       or mibdot1180MHzFrameTransmittedCountReg
       or mibdot11160MHzFrameTransmittedCountReg
       or mibdot1120MHzFrameReceivedCountReg
       or mibdot1140MHzFrameReceivedCountReg
       or mibdot1180MHzFrameReceivedCountReg
       or mibdot11160MHzFrameReceivedCountReg
       or mibrw20MHzFailedTXOPCountReg
       or mibrw20MHzSuccessfulTXOPCountReg
       or mibrw40MHzFailedTXOPCountReg
       or mibrw40MHzSuccessfulTXOPCountReg
       or mibrw80MHzFailedTXOPCountReg
       or mibrw80MHzSuccessfulTXOPCountReg
       or mibrw160MHzFailedTXOPCountReg
       or mibrw160MHzSuccessfulTXOPCountReg
       or mibrwDynBWDropCountReg
       or mibrwStaBWFailedCountReg
       or mibdot11DualCTSSuccessCountReg
       or mibdot11STBCCTSSuccessCountReg
       or mibdot11STBCCTSFailureCountReg
       or mibdot11nonSTBCCTSSuccessCountReg
       or mibdot11nonSTBCCTSFailureCountReg
    or mibIndexCurrent     )
             begin
   case(mibIndexCurrent)
          10'd1:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11WEPExcludedCountReg};
             end
          10'd2:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11FCSErrorCountReg};
             end
          10'd3:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibrwRxPHYErrorCountReg};
             end
          10'd4:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibrwRxFIFOOverflowCountReg};
             end
          10'd5:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibrwTxUnderrunCountReg};
      end
          10'd56:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11DualCTSSuccessCountReg};
             end
          10'd57:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11STBCCTSSuccessCountReg};
             end
          10'd58:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11STBCCTSFailureCountReg};
             end
          10'd59:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11nonSTBCCTSSuccessCountReg};
             end
          10'd60:
             begin
                mibIncrementCntRaw = {ZERO_CT[`IncWidth - 1 - 1:0],mibdot11nonSTBCCTSFailureCountReg};
             end
     default:
       begin 
         mibIncrementCntRaw = {`IncWidth{1'b0}};
       end
     endcase
  end
endmodule
                             