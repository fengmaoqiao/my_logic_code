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
// Description      : this block is in charge of data resynchronization from 
//                    host slave interface. it makes sure the first write access
//                    does not generate wait states
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
module postWrite( 

    //$port_g Clocks and Reset
    input wire                                      macPIClk,                  // Platform clock
    input wire                                      macPIClkHardRst_n,         // Platfrom Reset
    input wire                                      macCoreClk,                // Core clock
    input wire                                      macCoreClkHardRst_n,       // Core Reset

    //$port_g  slave interface
    input wire                                      regSel,                    // Select register block
    input wire                                      regWrite,                  // Write enable
    input wire                                      regRead,                   // Read enable
    input wire  [(`RW_REG_ADDR_WIDTH-2):0]          regAddr,                   // Register address
    input wire  [(`RW_REG_DATA_WIDTH-1):0]          regWriteData,              // Data to be written to the registers
    //
    output wire                                     regReadyIn,                // read data valid or write completed 
    output reg  [(`RW_REG_DATA_WIDTH-1):0]          regReadData,               // Data read from registers
    //$port_g Core Registers interface
    output reg                                      postWriteWrite,            // Write enable
    output reg                                      postWriteRead,             // Read enable
    output wire                                     postWriteSel,              // Sel enable
    output reg   [(`RW_REG_ADDR_WIDTH-2):0]         postWriteregAddr,          // Register address
    output reg   [(`RW_REG_DATA_WIDTH-1):0]         postWritewriteData,        // Data to be written to the registers
    //
    input  wire  [(`RW_REG_DATA_WIDTH-1):0]         postWritereadData          // Data read from registers
);

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire                           readEnable;             // Core reg selected for read
wire                           writeEnable;


reg                            regWrite_active;        //  trigger the resynchronization of the data
reg                            regRead_active;         //  trigger the resynchronization of the data


wire                           read_done;              //  indicate the resynchronization is done
wire                           write_done;             //  indicate the resynchronization is done

reg                            regReadDataValid;       //  trigger the resynchronization of the data
reg                            regWriteDataValid;      //  trigger the resynchronization of the data

reg [(`RW_REG_ADDR_WIDTH-2):0] postWriteregAddrmacPI;  // Register address
reg [(`RW_REG_DATA_WIDTH-1):0] postWritewriteDatamacPI;// Data to be written to the registers


wire                           postWriteWriteInt;      // Write enable
wire                           postWriteReadInt;       // Read enable

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// filter read and write request with the selection signal
assign readEnable  = regSel && regRead;
assign writeEnable = regSel && regWrite;

assign postWriteSel = postWriteRead || postWriteWrite;


// generate ready signal to host interface
assign regReadyIn =  (! regWrite_active) & (! (regWrite&regSel)) & (! regRead_active) & (! (readEnable));


// sample data to be written into registers on macPIClk
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
  begin
    postWritewriteDatamacPI <=  `RW_REG_DATA_WIDTH'b0;
    postWriteregAddrmacPI   <=  {(`RW_REG_ADDR_WIDTH-1){1'b0}};
    regWrite_active    <=  1'b0;
    regRead_active     <=  1'b0;
  end
  else 
  begin
    if (writeEnable == 1'b1)
    begin
      postWritewriteDatamacPI <= regWriteData;
      postWriteregAddrmacPI   <= regAddr;
      regWrite_active   <= 1'b1;
    end
    else if (readEnable == 1'b1)
    begin 
      postWriteregAddrmacPI  <= regAddr;
      regRead_active    <= 1'b1;
    end
    if (write_done)
      regWrite_active  <=  1'b0;
    if (read_done)
      regRead_active    <=  1'b0;
      
  end
end

// sample data to be written into registers on macCoreClk
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    postWritewriteData <=  `RW_REG_DATA_WIDTH'b0;
    postWriteregAddr   <=  {(`RW_REG_ADDR_WIDTH-1){1'b0}};
  end
  else 
  begin
    if (postWriteWriteInt == 1'b1)
    begin
      postWritewriteData <= postWritewriteDatamacPI;
      postWriteregAddr   <= postWriteregAddrmacPI;
    end
    else if (postWriteReadInt == 1'b1)
    begin 
      postWriteregAddr   <= postWriteregAddrmacPI;
    end
      
  end
end

// sample and maintain the data for the host if
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    regReadData        <= `RW_REG_DATA_WIDTH'b0;
    regReadDataValid   <= 1'b0;
    regWriteDataValid  <= 1'b0;
  end
  else 
  begin
    if (postWriteWrite == 1'b1)
      regWriteDataValid  <= 1'b1;
    else
      regWriteDataValid  <= 1'b0;
      
    if (postWriteRead == 1'b1)
    begin
      regReadData        <= postWritereadData;
      regReadDataValid   <= 1'b1;
    end 
    else
      regReadDataValid   <= 1'b0;
  end
end


// sample and maintain the data for the host if
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (macCoreClkHardRst_n == 1'b0)
  begin
    postWriteWrite    <= 1'b0;
    postWriteRead     <= 1'b0;
  end  
  else 
  begin
    postWriteRead     <= postWriteReadInt;
    postWriteWrite    <= postWriteWriteInt;
  end  
end

 
// resynchronize write request from hostif and generate
// a pulse to registers
pulse2PulseSynchro U_regWriteSynchro ( 
         .srcclk            (macPIClk),
         .srcresetn         (macPIClkHardRst_n),
         .dstclk            (macCoreClk),
         .dstresetn         (macCoreClkHardRst_n),
         .srcdata           (writeEnable),
         .dstdata           (postWriteWriteInt)
);

// resynchronize read request from hostif and generate
// a pulse to registers
pulse2PulseSynchro U_regReadSynchro ( 
         .srcclk            (macPIClk),
         .srcresetn         (macPIClkHardRst_n),
         .dstclk            (macCoreClk),
         .dstresetn         (macCoreClkHardRst_n),
         .srcdata           (readEnable),
         .dstdata           (postWriteReadInt)
);

// resynchronize the read signal to register to indicate 
// the host the end of transaction
fallingEdgeDetector U_regReadDataValidSynchro ( 
         .dstclk            (macPIClk),
         .dstresetn         (macPIClkHardRst_n),
         .srcdata           (regReadDataValid),
         .dstdata           (read_done)
);

// resynchronize the write signal to register to indicate 
// the host the end of transaction
fallingEdgeDetector U_postWriteWriteSynchro ( 
         .dstclk            (macPIClk),
         .dstresetn         (macPIClkHardRst_n),
         .srcdata           (regWriteDataValid),
         .dstdata           (write_done)
);





`ifdef RW_ASSERT_ON

//$rw_sva Checks for rxEnd signal asserted for a clock cycle
property no_write_while_synchro_not_done_prop; 
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  regWrite_active |=> !(regSel & regWrite);
endproperty
no_write_while_synchro_not_done: assert property (no_write_while_synchro_not_done_prop); 

//$rw_sva Checks for rxEnd signal asserted for a clock cycle
property no_read_while_synchro_not_done_prop; 
@(posedge macPIClk)
  disable iff(macPIClkHardRst_n==0)
  regWrite_active |=> !(regSel & regRead);
endproperty
no_read_while_synchro_not_done: assert property (no_read_while_synchro_not_done_prop); 

`endif // RW_ASSERT_ON


endmodule
