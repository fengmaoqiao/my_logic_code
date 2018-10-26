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
// Description      : Top level of fcs module
//                    This module calculates a running CRC-32 on input data,
//                    and accumulates it in internal registers.
//                    When fcsShift is asserted, it places the accumulated
//                    data byte by byte on output lines.
//                    
// Simulation Notes : 
//    For simulation, one define is available
//
//    RW_ASSERT_ON : which enables System Verilog Assertions.
//
// Synthesis Notes  :
// Application Note :                                                       
// Simulator        :                                                       
//     For simulation with RW_ASSERT_ON, the simulator must support System 
//     Verilog Assertions
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


module fcs( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreClk,              // MAC Core Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain 
                                                        // active low

            ///////////////////////////////////////////////
            //$port_g TX / RX Controller
            ///////////////////////////////////////////////
            input wire [7:0]   fcsDIn,                  // data input
            input wire         fcsDInValid,             // data input is valid

            input wire         fcsEnable,               // FCS enable
            input wire         fcsStart_p,              // Initialize CRC
            input wire         fcsShift,                // Shift CRC on fcsDOut controlled by TX Controller
            
            output wire        fcsOk,                   // FCS OK indication to RX Controller
            
            output reg [7:0]   fcsDOut,                 // data output to TX Controller
            output wire        fcsDOutValid,            // data valid
            output wire        fcsBusy,                 // FCS block busy
            output wire        fcsEnd_p,                // data generation end
            
            ///////////////////////////////////////////////
            //$port_g MAC-PHY Interface
            ///////////////////////////////////////////////
            input wire         mpIfTxFifoFull           // FIFO status
            );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
   parameter CRC_POLYNOMIAL    = 32'h04C1_1DB7,
             CRC_PRELOAD_VALUE = 32'hFFFF_FFFF,
             CRC_RESULT        = 32'hC704_DD7B;


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// reg
reg  [31:0] crcCalc;
reg  [31:0] crcCalcComb;
reg         shifting;
reg         shifting_ff1;
reg         accumulating;
reg  [2:0]  fcsCount;
reg         fcsDInValid_ff1;
reg         fcsDInValidKeep;

// wire
wire [31:0] crcPolynomial;
wire        crcEnable;
wire [7:0]  tempCrcCalc;
wire [7:0]  fcsDInMux;
wire        fcsEnd;

// integer
integer     i;
integer     j;


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


// The logic that is used to calculate the value of the CRC register for
// each 32 bit quantity that is latched in. The logic is as follows 
// Q <= F ( D, C, X ) where X is the crc polynomial, C is the
// current value of the crc register, and D is the word of data that
// has just been received.
   
// Assign the value of the crc polynomial to wire crcPolynomial
assign crcPolynomial = CRC_POLYNOMIAL; 

// if (crcCalc == CRC_RESULT) it indicates correct CRC value
assign fcsOk = fcsEnable && (crcCalc == CRC_RESULT);

// temporarily assigning crcCalc[31:24] to tempCrcCalc[7:0]
assign tempCrcCalc = ~crcCalc[31:24];

// when crcEnable signal is high contents of crcCalcComb are assigned to crcCalc.
assign crcEnable = fcsEnable && !mpIfTxFifoFull && 
                   (shifting || (accumulating && fcsDInValid));

// This counter is used while shift out CRC register
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    fcsCount <= 3'b0;
  else if (!fcsEnable || fcsStart_p || fcsEnd_p)
    fcsCount <= 3'b0;
  else if (shifting && !mpIfTxFifoFull)
    fcsCount <= fcsCount + 3'h1;
end

// fcsDInMux forces data input to 0 during shift step
assign fcsDInMux = (shifting) ? 8'b0 : fcsDIn;

// CRC polynomial
always @* 
begin
  crcCalcComb = crcCalc;
  for (i = 0; i < 8; i = i + 1) 
    crcCalcComb = ({crcCalcComb[30:0],1'b0}) ^
        (crcPolynomial[31:0] & 
        ({32{((fcsDInMux[i]^crcCalcComb[31]) & accumulating)}}));
end
 
// Latching the calculated/generated CRC into the CRC register
// whem crcEnable is high. On fcsStart_p CRC_PRELOAD_VALUE (32'hFFFF_FFFF)
// is assigned to crcCalc register. 
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    crcCalc <= 32'h0000_0000;
  else if (fcsStart_p)
    crcCalc <= CRC_PRELOAD_VALUE;
  else if (crcEnable)
    crcCalc <= crcCalcComb;
  else if (!fcsEnable)
    crcCalc <= 32'h0000_0000;
end

// Indicates that CRC register is accumulating
// This signal goes high on fcsStart_p and is pulled
// down when shift is set.  
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if(!macCoreClkHardRst_n)
    accumulating <= 1'b0;
  else if (fcsStart_p)
    accumulating <= 1'b1; 
  else if (fcsEnable)
    accumulating <= !(fcsShift && fcsDInValid) && accumulating;
  else
    accumulating <= 1'b0;
end

// generation of shifting signal
// This signal remains high until all 4 bytes of CRC
// are driven out.
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    shifting <= 1'b0;
  else if ((fcsEnd && !mpIfTxFifoFull) || fcsStart_p)
    shifting <= 1'b0;
  else if (fcsEnable)
  begin
    if (fcsShift && fcsDInValid)
      shifting <= 1'b1;
  end
  else
    shifting <= 1'b0;
end 

// Multiplexer to select between the incoming data and the generated CRC.
// When shifting is high the contents of tempCrcCalc is driven to fcsDOut else
// if shifting is low fcsDIn is drive out
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n )
begin
  if (!macCoreClkHardRst_n)
    fcsDOut <= 8'h0;
  else
  begin
    if (fcsEnable && !mpIfTxFifoFull)
    begin
      if (shifting)
      begin
        for (j=0; j<8; j=j+1)
        begin
          fcsDOut[j] <= tempCrcCalc[7-j];
        end
      end
      else if (fcsDInValid)
        fcsDOut <= fcsDIn;
    end
  end
end

// fcsDOutValid is active when MAC-PHY Interface FIFO is not full and
// when previous data was valid
assign fcsDOutValid = (fcsDInValid_ff1 || shifting_ff1 || fcsDInValidKeep) &&
                      !mpIfTxFifoFull;

// ff1 registers
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n )
begin
  if (!macCoreClkHardRst_n)
  begin
    fcsDInValid_ff1 <= 1'b0;
    shifting_ff1    <= 1'b0;
  end
  else
  begin
    fcsDInValid_ff1 <= fcsDInValid;
    shifting_ff1    <= shifting && !fcsEnd_p;
  end
end

// Keep one additional valid signal when MAC-PHY Interface FIFO if full
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n )
begin
  if (!macCoreClkHardRst_n)
    fcsDInValidKeep <= 1'b0;
  else
  begin
    if (fcsDInValid_ff1 && mpIfTxFifoFull)
      fcsDInValidKeep <= 1'b1;
    else if (!mpIfTxFifoFull)
      fcsDInValidKeep <= 1'b0;
  end
end

// FCS is busy when MAC-PHY Interface FIFO is full
assign fcsBusy = mpIfTxFifoFull || shifting_ff1;


// FCS end when fcsCount = 4
assign fcsEnd   = shifting_ff1 && (fcsCount == 3'h4);
// FCS end pulse generation for TX Controller
assign fcsEnd_p = fcsEnd && !mpIfTxFifoFull;


///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////
`ifdef RW_ASSERT_ON
default clocking cb @(posedge macCoreClk); endclocking

//$rw_sva Checks no data valid when fifo is full
property noValidWhenFull_prop;
@(posedge macCoreClk)
    mpIfTxFifoFull |-> !fcsDOutValid;
endproperty
noValidWhenFull: assert property (noValidWhenFull_prop);

`endif // RW_ASSERT_ON

endmodule
