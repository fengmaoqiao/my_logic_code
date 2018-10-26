//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $RCSmodulefile   : Key Search Engine
// $Author          : Karthik Kannan 
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 0.1                                                             
// $Date: 19-Nov-2008                                                                
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : Top level of Key Search Engine module
//                    
// Simulation Notes : 
//    KEY_INDEX_WIDTH : Configurable depth of Key Storage RAM
//
//    For simulation, two defines are available
//
//    RW_SIMU_ON      : which creates string signals to display the FSM states on  
//                      the waveform viewers
//    RW_ASSERT_ON    : which enables System Verilog Assertions.
//
//
// Synthesis Notes  :
//
// Application Note : 
//     All the signals are coming from MAC Controller clock domain. Hence, no
//     resynchronizations are needed.
//
// Simulator        :
//     
//
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

`define KEY_INDEX_WIDTH 6
  
module keySearchEngine ( 
          //$port_g Clock and Reset interface
          input wire          macCoreClk,            // MAC Core Clock
          input wire          macCoreClkHardRst_n,   // Hard Reset of the MAC WT Clock domain 
                                                     // active low
          input wire          macCoreClkSoftRst_n,   // Soft Reset of the MAC WT Clock domain 
                                                     // active low

          //$port_g CS Register Interface
          input wire          keyStoRAMReset,        // Active high reset signal to clear 
                                                     // RAM contents initiated by Software
          output wire         keyStoRAMResetIn,      // keyStoRAMReset clear value
          output wire         keyStoRAMResetInValid, // Clearing signal to CSReg, when the RAM reset
                                                     // operation is completed it is pulse
                                                     // for duration equal to 1 macCoreClk
          input wire [127:0]  encrKeyRAM,            // Crypto key configured by software
                                                     // into Encryption registers
`ifdef RW_WAPI_EN
          input wire [127:0]  encrIntKeyRAM,         // Integrity Crypto key configured by software
                                                     // into Encryption registers
`endif // RW_WAPI_EN
          input wire [`KEY_INDEX_WIDTH-1:0] keyIndexRAM, // Index of Key Storage RAM into which
                                                     // the encryption register contents
                                                     // are to be written
          input wire [47:0]   encrMACAddr,           // MAC address configured by software
                                                     // into Encryption registers
                                                     // It is reserved when keyIndexRAM points
                                                     // to default Key location
          input wire          newWrite,              // Trigger for write operation
                                                     // KS engine writes the encryption register
                                                     // inputs into RAM location pointed by
                                                     // keyIndexRAM
          input wire          newRead,               // Trigger for read operation
                                                     // KS engine reads the contents of RAM location 
                                                     // pointed by keyIndexRAM and copies them 
                                                     // to encryption register It provides the
                                                     // RAM contents on output lines of this
                                                     // module along with a validating signal
                                                     // CSR module should sample the contents 
                                                     // based on that signal
                                                     // CSReg shall not initiate a read operation
                                                     // without asserting the debugKSR signal below
          input wire          debugKSR,              // Signal to be asserted for debug purpose
                                                     // only initiated by Software. During a
                                                     // read operation, when this signal is
                                                     // asserted, valid key will be read out.
          output reg          newWriteInValid,       // Pulse signal to clear the newWrite
                                                     // signal initiated by CSReg
          output wire         newReadInValid,        // Pulse signal to clear the newRead
                                                     // signal initiated by CSReg
          input wire          cLenRAM,               // Cipher length indication for WEP
                                                     // 0 - 64-bit WEP encryption/decryption
                                                     // 1 - 128-bit WEP encryption/decryption
          input wire          useDefKeyRAM,          // Indication for usage of Default Keys.
          input wire [1:0]    sppRAM,                // Indication for handling A-MSDU frames
          input wire [3:0]    vlanIDRAM,             // Virtual LAN ID for searching default key
          input wire [2:0]    cTypeRAM,              // Cipher type

          output wire         keyRegReadValid_p,     // Pulse signal indicating completion of 
                                                     // read operation Validates output 
                                                     // contents like cTypeRAMIn, 
                                                     // keyIndexReturn, cLenRAMIn, 
                                                     // macAddressKSR etc.
          output wire [2:0]   cTypeRAMIn,            // Cipher Type found at Index or value at
                                                     // at MAC address found location
          output wire [3:0]   vlanIDRAMIn,           // Virtual LAN ID found at Index or value 
                                                     // at MAC address found location
          output wire [1:0]   sppRAMIn,              // SPP RAM value found at Index or value 
                                                     // at MAC address found location
          output wire         useDefKeyRAMIn,        // Use Default Key Value found at Index 
                                                     // or value at MAC address found location
          output wire         cLenRAMIn,             // Cipher length found at Index or value 
                                                     // at MAC address found location
          output wire [47:0]  encrMACAddrIn,         // MAC address value found at Index
          output wire [127:0] encrKeyRAMIn,          // Value of crypto key at Index found or
                                                     // value at MAC address found location
`ifdef RW_WAPI_EN
          output wire [127:0] encrIntKeyRAMIn,       // Value of integrity crypto key at Index found or
                                                     // value at MAC address found location
`endif // RW_WAPI_EN

          //$port_g Controller Interface [TX or RX or Block ACK]
          input wire [`KEY_INDEX_WIDTH-1:0] keySearchIndex, // RAM Index to be searched
          input wire         keySearchIndexTrig_p,  // Trigger for searching RAM index and
                                                    // return contents (along with MAC addr)
          input wire [47:0]  macAddressIn,          // MAC address to be searched in RAM
          input wire         indexSearchTrig_p,     // Trigger for searching MAC address in
                                                    // KS RAM and return contents (along with
                                                    // Index)
          output wire        keyStorageError_p,     // Error indicating key NOT found /
                                                    // MAC address NOT found
          output wire        keyStorageValid_p,     // Pulse signal indicating completion of 
                                                    // search operation Validates output 
                                                    // contents like cTypeKSR, 
                                                    // keyIndexReturn, cLenKSR, 
                                                    // macAddressKSR etc.
          output reg [`KEY_INDEX_WIDTH-1:0] keyIndexReturn, // RAM Index output corresponding to
                                                    // location where MAC address was found
          output reg [2:0]   cTypeKSR,              // Cipher Type found at Index or value at
                                                    // at MAC address found location
          output reg [3:0]   vlanIDKSR,             // Virtual LAN ID found at Index or value 
                                                    // at MAC address found location
          output reg [1:0]   sppKSR,                // SPP RAM value found at Index or value 
                                                    // at MAC address found location
          output reg         useDefKeyKSR,          // Use Default Key Value found at Index 
                                                    // or value at MAC address found location
          output reg         cLenKSR,               // Cipher length found at Index or value 
                                                    // at MAC address found location
          output reg [47:0]  macAddressKSR,         // MAC address value found at Index
          output reg [127:0] cryptoKeyKSR,          // Value of crypto key at Index found or
                                                    // value at MAC address found location
`ifdef RW_WAPI_EN
          output reg [127:0] cryptoIntKeyKSR,       // Value of integrity crypto key at Index found or
                                                    // value at MAC address found location
`endif // RW_WAPI_EN
          
          //$port_g Single Port RAM Interface [Key Storage RAM]
`ifdef RW_WAPI_EN
          input  wire [314:0] keyStorageReadData,   // Read data bus from KS RAM
          output reg  [314:0] keyStorageWriteData,  // Write data bus to KS RAM
`else
          input  wire [186:0] keyStorageReadData,   // Read data bus from KS RAM
          output reg  [186:0] keyStorageWriteData,  // Write data bus to KS RAM
`endif // RW_WAPI_EN
          output reg  [`KEY_INDEX_WIDTH-1:0] keyStorageAddr, // Address bus to KS RAM
          output reg          keyStorageEn,         // Enable (access) to KS RAM
                                                    // Active high for both read/write
          output reg          keyStorageWriteEn,    // Write enable to KS RAM
                                                    // Active high only for write

          output wire  [15:0] debugPortKeySearch    // Debug port for validation
    );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// Key Search FSM Description
//$fsm_sd keySearchEngine
localparam    
              KS_IDLE                     =  3'd0,
              KS_INIT                     =  3'd1,
              RD_WR_KS_RAM                =  3'd2,
              RD_INDEX_OR_SEARCH_MAC_ADDR =  3'd3,
              KS_WAIT_SAMPLING            =  3'd4;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

   reg [2:0]                  keySearchEngCs;
   reg [2:0]                  keySearchEngNs;
   reg [`KEY_INDEX_WIDTH-1:0] currAddr;
   reg [47:0]                 macAddressInLat;
   reg                        indexReadLat;
   
   reg                        macAddrSearchInProg;
   reg                        keyStorageOutLat;
   reg                        csrAccessLat;
   reg [`KEY_INDEX_WIDTH-1:0] keyIndexLat;
   reg                        keyRAMReadbySW;
  
   wire                       indexChk;
   wire                       macAddrFound;
   wire                       readWriteRAM;
   reg                        keySearchComplete,searchStarted;
   reg [`KEY_INDEX_WIDTH-1:0] lastMacAddrFoundAt;

   reg                        keyRegReadValid_ff1_p;
   reg                        keyStorageValid_ff1_p;
   reg                        keyStorageError_ff1_p;
   reg                        keyStoRAMResetInValid_ff1;
 
   reg [1:0]                  waitSamplingCnt;
   
//////////////////////////////////////////////////////////////////////////////
// Beginning of Logic part
//////////////////////////////////////////////////////////////////////////////

assign debugPortKeySearch = {indexSearchTrig_p,
                             keySearchIndexTrig_p,
                             keyStorageAddr[5:0],
                             keyStorageError_p,
                             keyStorageValid_p,
                             keyIndexReturn[5:0]
                            };

//////////////////////////////
// Key Search FSM
//////////////////////////////

// Key Search FSM Current State Logic 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    keySearchEngCs <= KS_IDLE; 
  else if (macCoreClkSoftRst_n == 1'b0) // Synchronous Reset
    keySearchEngCs <= KS_IDLE;
  else
    keySearchEngCs <= keySearchEngNs; 
end

// Key Search FSM Next State Logic
always @*
begin
  case(keySearchEngCs)
    KS_IDLE:
      //$fsm_s in KS_IDLE the KS Engine wait either for reset RAM (reinit keyRAM) or triggers from controllers to read the keyRAM, or SW read/write to the keyRAM
      if(keyStoRAMReset == 1'b1)
        //$fsm_t If keyStoRAMReset is set then the KS Engine jumps to KS_INIT
        keySearchEngNs =  KS_INIT;
      else if((keySearchIndexTrig_p == 1'b1) || (indexSearchTrig_p == 1'b1))
        //$fsm_t If keySearchIndexTrig_p or indexSearchTrig_p is pulsed then the KS Engine jumps to RD_INDEX_OR_SEARCH_MAC_ADDR
        keySearchEngNs =  RD_INDEX_OR_SEARCH_MAC_ADDR;
      else if(
              (((newWrite && !newWriteInValid) || csrAccessLat) )
              || (newRead && !newReadInValid )
              )
        //$fsm_t If SW read/write access then KS Engine jumps to RD_WR_KS_RAM
        keySearchEngNs =  RD_WR_KS_RAM;
      else
        //$fsm_t If no triggers or RAM reset or SW access then it remains in KS_IDLE
        keySearchEngNs = KS_IDLE;

    KS_INIT:
      //$fsm_s in KS_INIT the KS Engine writes default value to all keyRAM address. The default value = 186'h{2'h0,4'h0,2'h0,1'h0,1'h0,48'hFFFF_FFFF_FFFF,128'h0}
      if(keyStoRAMResetInValid_ff1 == 1'b1)
        //$fsm_t When the keyRAM address reaches the last one, then KS Engines goes back to KS_IDLE
        keySearchEngNs =  KS_IDLE;
      else 
        //$fsm_t When the keyRAM address is not the last one the KS Engines stays in KS_INIT
        keySearchEngNs =  KS_INIT;

    RD_WR_KS_RAM:
      //$fsm_s The RD_WR_KS_RAM is reached when there is a write access or a debug read operation initiated by CSR module
      if((keySearchIndexTrig_p == 1'b1) || (indexSearchTrig_p == 1'b1))
        //$fsm_t if keySearchIndexTrig_p or indexSearchTrig_p is received then jumps to RD_INDEX_OR_SEARCH_MAC_ADDR
        keySearchEngNs =  RD_INDEX_OR_SEARCH_MAC_ADDR;
      else if (newRead)
        //$fsm_t if newRead then goes to KS_WAIT_SAMPLING
        keySearchEngNs =  KS_WAIT_SAMPLING;
      else
        //$fsm_t if no newRead or triggers then goes back to KS_IDLE
        keySearchEngNs =  KS_IDLE;

    RD_INDEX_OR_SEARCH_MAC_ADDR:
      //$fsm_s This state is reached when either of the following operations are initiated 
      // 1) MAC address search [Transmitter address as input trigger]
      //      It may take a minimum of 3 clocks to 68 clock cycles
      // 2) Index search [RAM Index as input trigger]
      //      It takes 3 clock cycles for a valid output
      if(indexReadLat == 1'b1)
        //$fsm_t if indexReadLat (index keyRAM read done) then goes back to KS_IDLE.
        keySearchEngNs = KS_IDLE;
      else if(keyStorageError_ff1_p == 1'b1)
        //$fsm_t if keyStorageError_ff1_p (MAC address search not found) then goes back to KS_IDLE.
        keySearchEngNs = KS_IDLE;
      else if(keySearchComplete == 1'b1)
        //$fsm_t if keySearchComplete (MAC address search found) then goes back to KS_IDLE.
        keySearchEngNs = KS_IDLE;
      else
        //$fsm_t if index read not done or MAC address search not done then remains in RD_INDEX_OR_SEARCH_MAC_ADDR.
        keySearchEngNs = RD_INDEX_OR_SEARCH_MAC_ADDR;
    
    KS_WAIT_SAMPLING:
      //$fsm_s This state is reached when there is a read access in order let time to sample data
      if(waitSamplingCnt == 2'h2)
        //$fsm_t if waitSamplingCnt reaches 2 then goes to KS_IDLE
        keySearchEngNs =  KS_IDLE;
      else
        //$fsm_t if waitSamplingCnt is not 2 then remains in KS_WAIT_SAMPLING
        keySearchEngNs =  KS_WAIT_SAMPLING;

     // Disable coverage on the default state because it cannot be reached.
     // pragma coverage block = off 
    default:   
        keySearchEngNs = KS_IDLE;
     // pragma coverage block = on 
  endcase
end
   
   // Logic to CSR for clearing keyStoRAMReset
   // Asserted once RAM reset operation is completed by KS engine
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)  
     keyStoRAMResetInValid_ff1 <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0)
     keyStoRAMResetInValid_ff1 <= 1'b0;
   // Assert clear pulse when address reaches 'hFF [63 - Highest port no.]
   else if((keySearchEngCs == KS_INIT) && (&keyStorageAddr)) 
     keyStoRAMResetInValid_ff1 <= 1'b1;
   else
     keyStoRAMResetInValid_ff1 <= 1'b0;
end

assign keyStoRAMResetInValid = keyStoRAMResetInValid_ff1; 

assign keyStoRAMResetIn = 1'b0;

   // Logic to let correct sampling on MAC COre clk domain
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)  
     waitSamplingCnt <= 2'b0;
   else if (macCoreClkSoftRst_n == 1'b0)
     waitSamplingCnt <= 2'b0;
   else if((keySearchEngCs == KS_WAIT_SAMPLING) && (waitSamplingCnt < 2'h3)) 
     waitSamplingCnt <= waitSamplingCnt + 2'h1;
   else
     waitSamplingCnt <= 2'b0;
end


   // Pulse to clear CSR signal 'newWrite' if write operation is complete
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)
     newWriteInValid <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0)
     newWriteInValid <= 1'b0;
   else if (((keySearchEngCs == RD_WR_KS_RAM) && keyStorageWriteEn) ||
            ((keySearchEngCs == KS_WAIT_SAMPLING) && newWrite))
     newWriteInValid <= 1'b1;
   else
     newWriteInValid <= 1'b0;
end
   
   // Pulse to clear CSR signal 'newRead' if read operation is complete
assign newReadInValid = ((keySearchEngCs == RD_WR_KS_RAM) || (keySearchEngCs == KS_WAIT_SAMPLING)) && keyStorageEn && !keyStorageWriteEn;

   // Logic to handle a situation when RAM Search and RAM update
   // occur simultaneously - It stores the update and completes the search
   // operation first. This keyIndexLat is used during the
   // update that occurs at the end the search operation
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) begin
      csrAccessLat <= 1'b0;
      keyIndexLat <= {`KEY_INDEX_WIDTH'b0};
   end      
   else if (macCoreClkSoftRst_n == 1'b0) begin
      csrAccessLat <= 1'b0;
      keyIndexLat <= {`KEY_INDEX_WIDTH'b0};
   end
   else if (newWrite || newRead) begin
           if (indexChk || indexSearchTrig_p)
             csrAccessLat <= 1'b1;
           else
             csrAccessLat <= 1'b0;
      keyIndexLat <= keyIndexRAM;
   end
   else if ((keySearchEngCs == RD_WR_KS_RAM) && 
            (keyStorageEn == 1'b1)) begin
      csrAccessLat <= 1'b0;
      keyIndexLat <= {`KEY_INDEX_WIDTH'b0};
   end     
end

   // Logic for latching macAddressIn - Input MAC address to be searched
   // in the Key Storage RAM
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)
      macAddressInLat <= 48'h0;
   else if (macCoreClkSoftRst_n == 1'b0) 
      macAddressInLat <= 48'h0;
   else if (indexSearchTrig_p == 1'b1)
      macAddressInLat[47:0] <= macAddressIn[47:0];
end

   // Signal indicating Index Search operation
   // Used to switch FSM to IDLE [this is 2 clock process]
   // Valid output would be available on the 3rd clock cycle
   // Also used to differentiate control mechanism of address bus
   // enable signals to RAM during RD_INDEX_OR_SEARCH_MAC_ADDR state
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)
     indexReadLat <= 1'h0;
   else if (macCoreClkSoftRst_n == 1'b0) 
     indexReadLat <= 1'h0;
   else if ((keySearchIndexTrig_p == 1'b1) && (macAddrSearchInProg == 1'b0))
     indexReadLat <= 1'h1;
   else if (keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR)
     indexReadLat <= 1'h0;
end

   // Logic to indicate MAC address search is in progress
   // This is asserted only during MAC address search operation
   // That is, it is a latched signal that stays high during the
   // entire search operation (upto a max. of 68 clock cycles)
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) 
      macAddrSearchInProg <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0) 
      macAddrSearchInProg <= 1'b0;
   else begin
      if (indexSearchTrig_p)
         macAddrSearchInProg <= 1'b1;
      else if ((keySearchComplete == 1'b1) ||
               (keyStorageError_ff1_p == 1'b1))
         macAddrSearchInProg <= 1'b0;
   end
end

   // Logic to detect the event of finding MAC address in RAM
   // Added here to reduce the complexity in block where it is used
assign macAddrFound = ((keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR) && 
                       (searchStarted != 1'b0) &&
                       (macAddressInLat[47:0] == keyStorageReadData[58:11]));

   // Logic to detect completion of MAC address search operation
   // It is a registered version of macAddrFound signal above
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) 
     keySearchComplete <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0) 
     keySearchComplete <= 1'b0;
   else if (macAddrFound)
     keySearchComplete <= 1'b1;
   else
     keySearchComplete <= 1'b0;
end
   
   // Logic to ensure no previous stray search values are sampled
   // during a re-search operation
   // Generated only during MAC address search operation 
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) 
     searchStarted <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0) 
     searchStarted <= 1'b0;
   else if((keySearchComplete == 1'b1) ||
           (keyStorageError_ff1_p == 1'b1))
     searchStarted <= 1'b0;
   else if ((keyStorageWriteEn == 1'b0) && 
            (keyStorageEn == 1'b1) &&
            (keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR) && 
            (macAddrSearchInProg == 1'b1))   
     searchStarted <= 1'b1;
end

   // Logic to store last searched address to be used in checking error
   // cases where MAC address is not found
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) 
     lastMacAddrFoundAt <= {`KEY_INDEX_WIDTH{1'b1}};
   else if (macCoreClkSoftRst_n == 1'b0) 
     lastMacAddrFoundAt <= {`KEY_INDEX_WIDTH{1'b1}};
   else if(keyStoRAMReset)
     lastMacAddrFoundAt <= {`KEY_INDEX_WIDTH{1'b1}};
   else if (indexSearchTrig_p == 1'b1)
   begin
     if(currAddr <= {`KEY_INDEX_WIDTH'd24})
       lastMacAddrFoundAt <= {`KEY_INDEX_WIDTH'd24};
     else
       lastMacAddrFoundAt <= currAddr;
   end
end

   // Logic for the event - Null key / MAC address not found in RAM   
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) 
     keyStorageError_ff1_p <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0) 
     keyStorageError_ff1_p <= 1'b0;
   else if ((searchStarted     == 1'b1)                     &&   // searching
            (keyStorageAddr    == lastMacAddrFoundAt)       &&   // last index reached
            (keySearchComplete == 1'b0)                     &&   // search not completed
            (macAddrFound      == 1'b0)                        ) // no mac address found
     keyStorageError_ff1_p <= 1'b1;
   else
     keyStorageError_ff1_p <= 1'b0;
end

assign keyStorageError_p = keyStorageError_ff1_p; 

   // Key Storage - Write operation from CSR
   // CSR Write operations take single clock for updating the RAM.
   // RAM reset mechanism may also be initiated by software through the
   // signal keyStoRAMReset, for initialization of RAM contents
   // to default values.
 
`ifdef RW_WAPI_EN
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) begin
      keyStorageWriteData[314:0] <= 315'h0;
      keyStorageWriteEn <= 1'b0;
   end
   else if (macCoreClkSoftRst_n == 1'b0) begin
      keyStorageWriteData[314:0] <= 315'h0;
      keyStorageWriteEn <= 1'b0;
   end
   else begin
     case (keySearchEngNs)
       KS_INIT: begin
            keyStorageWriteData[314:0] <= {128'h0,128'h0,48'hFFFF_FFFF_FFFF,1'h0,1'h0,2'h0,4'h0,3'h0};
            keyStorageWriteEn          <= 1'b1;
       end            
       RD_WR_KS_RAM: begin
            keyStorageWriteData[314:0] <= { encrIntKeyRAM[127:0],
                                               encrKeyRAM[127:0],
                                              encrMACAddr[47:0],
                                                  cLenRAM,
                                             useDefKeyRAM,
                                                   sppRAM[1:0],
                                                vlanIDRAM[3:0], 
                                                 cTypeRAM[2:0]  };
          if(((newWrite == 1'b1) || (csrAccessLat == 1'b1))
             && (newRead == 1'b0))
            keyStorageWriteEn <= 1'b1;
          else
            keyStorageWriteEn <= 1'b0;
       end
       default: begin
            keyStorageWriteData[314:0] <= 315'h0;
            keyStorageWriteEn <= 1'b0;
       end
     endcase
   end
end
`else
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) begin
      keyStorageWriteData[186:0] <= 187'h0;
      keyStorageWriteEn <= 1'b0;
   end
   else if (macCoreClkSoftRst_n == 1'b0) begin
      keyStorageWriteData[186:0] <= 187'h0;
      keyStorageWriteEn <= 1'b0;
   end
   else begin
     case (keySearchEngNs)
       KS_INIT: begin
            keyStorageWriteData[186:0] <= {128'h0,48'hFFFF_FFFF_FFFF,1'h0,1'h0,2'h0,4'h0,3'h0};
            keyStorageWriteEn          <= 1'b1;
       end            
       RD_WR_KS_RAM: begin
            keyStorageWriteData[186:0] <= {    encrKeyRAM[127:0],
                                              encrMACAddr[47:0],
                                                  cLenRAM,
                                             useDefKeyRAM,
                                                   sppRAM[1:0],
                                                vlanIDRAM[3:0], 
                                                 cTypeRAM[2:0]  };
          if(((newWrite == 1'b1) || (csrAccessLat == 1'b1))
             && (newRead == 1'b0))
            keyStorageWriteEn <= 1'b1;
          else
            keyStorageWriteEn <= 1'b0;
       end
       default: begin
            keyStorageWriteData[186:0] <= 187'h0;
            keyStorageWriteEn <= 1'b0;
       end
     endcase
   end
end
`endif // RW_WAPI_EN

   // Logic for driving enable signal for accessing RAM port
   // (for either read or write or search operations)
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)  
      keyStorageEn <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0)
      keyStorageEn <= 1'b0;
   else begin
     case (keySearchEngNs)
       KS_INIT:
         keyStorageEn <= 1'b1;
       RD_WR_KS_RAM:
         keyStorageEn <= 1'b1;
       RD_INDEX_OR_SEARCH_MAC_ADDR:
         keyStorageEn <= 1'b1;
       KS_WAIT_SAMPLING:
         keyStorageEn <= 1'b1;
       default:
         keyStorageEn <= 1'b0;
     endcase
   end
end   

   // Logic for detecting trigger for Index search event
   // Added here to reduce the complexity in block where it is used
assign indexChk = (macAddrSearchInProg == 1'b0) &&
                  (keySearchEngNs == RD_INDEX_OR_SEARCH_MAC_ADDR) && 
                  (keySearchIndexTrig_p == 1'b1);

   // Logic for detecting CSR access for debug read or RAM update (write)
   // Added here to reduce the complexity in block where it is used
assign readWriteRAM = ((newRead && (keySearchEngNs == RD_WR_KS_RAM))     ||
                                   (keySearchEngNs == KS_WAIT_SAMPLING)) || 
                      (newWrite && (keySearchEngNs == RD_WR_KS_RAM));

   // Logic for driving address signals to Key Storage RAM
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0)  
      keyStorageAddr <= {`KEY_INDEX_WIDTH'b0};
   else if (macCoreClkSoftRst_n == 1'b0)
      keyStorageAddr <= {`KEY_INDEX_WIDTH'b0};
   else begin
         if ((macAddrFound == 1'b1) || 
             (keyStorageError_ff1_p == 1'b1) ||
             (keySearchComplete == 1'b1))
           keyStorageAddr <= currAddr;
         else if(indexChk == 1'b1) 
           keyStorageAddr <= keySearchIndex;
         else if(readWriteRAM == 1'b1)
           keyStorageAddr <= keyIndexRAM;
         else if(
                 (keyStorageEn == 1'b1) && 
                 (indexReadLat == 1'b0) &&
                 (keyStoRAMResetInValid_ff1 == 1'b0) && 
                 ((keySearchEngCs == KS_INIT) || 
                  (keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR))
                )
         begin
           if((keyStorageAddr == {`KEY_INDEX_WIDTH{1'b1}}) && (keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR))
             keyStorageAddr <= {`KEY_INDEX_WIDTH'd24};
           else
             keyStorageAddr <= keyStorageAddr + `KEY_INDEX_WIDTH'b1;
         end
         else if (indexSearchTrig_p == 1'b1)
         begin
           if(currAddr < {`KEY_INDEX_WIDTH'd24})
             keyStorageAddr <= {`KEY_INDEX_WIDTH'd24};
           else
             keyStorageAddr <= currAddr;
         end
         else if (macAddrSearchInProg == 1'b1)
           keyStorageAddr <= currAddr;
         else if(csrAccessLat == 1'b1)
           keyStorageAddr <= keyIndexLat;
         else 
           keyStorageAddr <= {`KEY_INDEX_WIDTH'b0};
   end
end

   // Current Address - Latched version of keyStorageAddr RAM 
   // These counters are maintained after every Key/MAC address search
   // operation - to be used later during re-search
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
   if (macCoreClkHardRst_n == 1'b0) 
     currAddr <= {`KEY_INDEX_WIDTH'b0};
   else if (macCoreClkSoftRst_n == 1'b0)
     currAddr <= {`KEY_INDEX_WIDTH'b0};
   else if (indexSearchTrig_p == 1'b1)
   begin
     if(currAddr < {`KEY_INDEX_WIDTH'd24})
       currAddr <= {`KEY_INDEX_WIDTH'd24};
   end
   else if ((keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR) && 
            (keyStorageEn == 1'b1) && 
            (macAddrFound == 1'b0) &&
            (keyStorageError_ff1_p == 1'b0))
     currAddr <= keyStorageAddr;
end
   
   // Preliminary signal for validating Key Storage Output
   // Outputs need to be flopped once after reading from
   // the Single Port RAM to ensure data integrity
   // Hence following keyStorageOutLat is flopped again below
   // to output the Key Storage RAM contents to other module
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
  begin
   if (macCoreClkHardRst_n == 1'b0)
     keyStorageOutLat  <= 1'b0;
   else if (macCoreClkSoftRst_n == 1'b0)
     keyStorageOutLat  <= 1'b0;
   else if (keyStorageError_ff1_p == 1'b1)
     keyStorageOutLat  <= 1'b0;
   else if ((keyStorageWriteEn == 1'b0) && 
            (keyStorageEn == 1'b1)) begin
           if (keySearchEngCs == RD_INDEX_OR_SEARCH_MAC_ADDR)
             begin
                if((macAddrSearchInProg == 1'b1) &&
                   (keySearchComplete == 1'b1))
                  keyStorageOutLat <= 1'b1;
                else if(macAddrSearchInProg == 1'b0)
                  keyStorageOutLat <= 1'b1;
             end
           else if (keySearchEngCs == RD_WR_KS_RAM) 
             keyStorageOutLat <= 1'b1;
           end
   else
     keyStorageOutLat <= 1'b0;
end

   // Key Storage - Read operation from CSR / TX or RX or Block ACK Controller
   // Data latency details @ 100Mhz MAC Clock (for valid data at output lines):
   // ---------------------------------------------------------------
   // CSR reads - Three clock cycles (after the read pulse) [30ns]
   // ---------------------------------------------------------------

   // ---------------------------------------------------------------
   // Index search operations - Three clock cycles after trigger pulse [30ns]
   // ---------------------------------------------------------------

   // ---------------------------------------------------------------
   // Access from TX / RX / Block ACK controller may take more time
   // like Re-search operations (MAC address search)
   // can take upto a maximum of 68 clocks [680ns @ 100Mhz MAC Clock]
   // (for a max. of 64 station MAC addresses stored in KS RAM)
   // ---------------------------------------------------------------

 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       keyRegReadValid_ff1_p <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       keyRegReadValid_ff1_p <= 1'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       keyRegReadValid_ff1_p <= 1'b0;
    else if ((keyStorageOutLat == 1'b1) && keyRAMReadbySW)  
       keyRegReadValid_ff1_p <= 1'b1;
    else 
       keyRegReadValid_ff1_p <= 1'b0;
 end

 assign keyRegReadValid_p = keyRegReadValid_ff1_p; 

 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       keyStorageValid_ff1_p <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       keyStorageValid_ff1_p <= 1'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       keyStorageValid_ff1_p <= 1'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW)   
       keyStorageValid_ff1_p <= 1'b1;
    else 
       keyStorageValid_ff1_p <= 1'b0;
 end

 assign keyStorageValid_p = keyStorageValid_ff1_p; 

   // Key Index pointing to the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       keyIndexReturn <= {`KEY_INDEX_WIDTH'b0};
    else if (macCoreClkSoftRst_n == 1'b0) 
       keyIndexReturn <= {`KEY_INDEX_WIDTH'b0};
    else if (keyStorageError_ff1_p == 1'b1) 
       keyIndexReturn <= {`KEY_INDEX_WIDTH'b0};
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       keyIndexReturn <= currAddr;
 end

   // Cipher Type Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       cTypeKSR <= 3'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       cTypeKSR <= 3'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       cTypeKSR <= 3'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       cTypeKSR <= keyStorageReadData[2:0];
 end
 
 assign cTypeRAMIn = (newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) ? keyStorageReadData[2:0] : 3'b0;

   // Virtual LanID Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       vlanIDKSR <= 4'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       vlanIDKSR <= 4'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       vlanIDKSR <= 4'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       vlanIDKSR <= keyStorageReadData[6:3];
 end
 
 assign vlanIDRAMIn = (newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) ? keyStorageReadData[6:3] : 4'b0;

   // SPP Type Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       sppKSR <= 2'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       sppKSR <= 2'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       sppKSR <= 2'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       sppKSR <= keyStorageReadData[8:7];
 end
 
 assign sppRAMIn = (newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) ? keyStorageReadData[8:7] : 2'b0;

   // UseDefaultKey Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       useDefKeyKSR <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       useDefKeyKSR <= 1'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       useDefKeyKSR <= 1'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       useDefKeyKSR <= keyStorageReadData[9];
 end
 
 assign useDefKeyRAMIn = (newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) ? keyStorageReadData[9] : 1'b0;

   // Cipher Length Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       cLenKSR <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       cLenKSR <= 1'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       cLenKSR <= 1'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       cLenKSR <= keyStorageReadData[10];
 end
 
 assign cLenRAMIn = (newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) ? keyStorageReadData[10] : 1'b0;

   // MAC Address Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       macAddressKSR <= 48'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       macAddressKSR <= 48'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       macAddressKSR <= 48'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW) 
       macAddressKSR <= keyStorageReadData[58:11];
 end
 
 assign encrMACAddrIn = (newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) ? keyStorageReadData[58:11] : 48'b0;

   // Encryption Key Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       cryptoKeyKSR <= 128'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       cryptoKeyKSR <= 128'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       cryptoKeyKSR <= 128'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW)
       cryptoKeyKSR <= keyStorageReadData[186:59];
 end
 
 assign encrKeyRAMIn    = ((newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) && debugKSR) ? keyStorageReadData[186:59]  : 128'b0 ;
`ifdef RW_WAPI_EN
   // Encryption Key Field of the last successfully searched
   // RAM location; registered version of the RAM's row content
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       cryptoIntKeyKSR <= 128'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       cryptoIntKeyKSR <= 128'b0;
    else if (keyStorageError_ff1_p == 1'b1) 
       cryptoIntKeyKSR <= 128'b0;
    else if ((keyStorageOutLat == 1'b1) && !keyRAMReadbySW)
       cryptoIntKeyKSR <= keyStorageReadData[314:187];
 end
 
 assign encrIntKeyRAMIn = ((newRead || (keySearchEngCs ==  KS_WAIT_SAMPLING)) && debugKSR) ? keyStorageReadData[314:187] : 128'b0 ;
`endif // RW_WAPI_EN

   // Logic to prevent unauthorized access to encryption key 
   // stored in Key Storage RAM
   // The signal below is used above to ensure crypto key
   // is provided as output only when authorized access is
   // sensed from the software (authenticated by debugKSR = 1)
   // When CSR read is observed and debugKSR = 0, an invalid 
   // crypto key is given as output to SW
 always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
 begin
    if (macCoreClkHardRst_n == 1'b0) 
       keyRAMReadbySW <= 1'b0;
    else if (macCoreClkSoftRst_n == 1'b0) 
       keyRAMReadbySW <= 1'b0;
    else if (newReadInValid && keyStorageOutLat) 
       keyRAMReadbySW <= 1'b0;
    else if (keyStorageError_ff1_p) 
       keyRAMReadbySW <= 1'b0;
    else if ((keySearchEngCs == RD_WR_KS_RAM) && newRead) 
       keyRAMReadbySW <= 1'b1;
 end
               
            
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Display FSM State in string for RTL simulation waveform
//////////////////////////////////////////////////////////
`ifdef RW_SIMU_ON
  // This signal is defined to ease the simulation and waveform analysis.
  // String definition to display keySearchEng current state
   reg [27*8:0] keySearchEngCs_str;
   
// Key Search FSM states displayed in a string to easy simulation and debug
always @ (keySearchEngCs)
begin
  case (keySearchEngCs)
                      KS_IDLE  :  keySearchEngCs_str = {"KS_IDLE"};
                      KS_INIT  :  keySearchEngCs_str = {"KS_INIT"};
                 RD_WR_KS_RAM  :  keySearchEngCs_str = {"RD_WR_KS_RAM"};
  RD_INDEX_OR_SEARCH_MAC_ADDR  :  keySearchEngCs_str = {"RD_INDEX_OR_SEARCH_MAC_ADDR"};
             KS_WAIT_SAMPLING  :  keySearchEngCs_str = {"KS_WAIT_SAMPLING"};
                      default  :  keySearchEngCs_str = {"XXXX"};
   endcase
end

`endif // RW_SIMU_ON


// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON

   // Checks if there is no simultaneous read or write initiated by Software/CSR
   property noSimultaneousCsrReadWrite_prop;
   @(posedge macCoreClk)
     (newWrite == 1'b1) |-> (newRead == 1'b0);
   endproperty
   noSimultaneousCsrReadWrite: assert property (noSimultaneousCsrReadWrite_prop);

   // Checks if there is no simultaneous assertions of Index and MAC address search
   property checkIndexAndMACAddressSearch_prop;
   @(posedge macCoreClk)
     (indexSearchTrig_p == 1'b1) |-> (keySearchIndexTrig_p == 1'b0);
   endproperty
   checkIndexAndMACAddressSearch: assert property (checkIndexAndMACAddressSearch_prop);
   
`endif
endmodule
                 

