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
// Description      : 
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

module divider #(parameter NBIT_WIDTH = 20, parameter NBITPSYMB_WIDTH = 12) (
          //$port_g Clock and Reset interface
          input  wire                       macCoreClk,          // MAC Platform Interface Transmit Clock
          input  wire                       macCoreClkHardRst_n, // Hard Reset of the MAC Platform Interface Clock domain 
                                                                 // active low

          //$port_g TXTimeCalculation interface
          input  wire                       startDiv_p,          // Start the processing
          input  wire                       roundUp,             // Indicates the round up of the result
          input  wire      [NBIT_WIDTH-1:0] nBit,                // Number of Bits
          input  wire [NBITPSYMB_WIDTH-1:0] nBitPSymb,           // Number of Bits per Symb
          input  wire                 [3:0] initCnt,             // Start counter initialization value
          output reg       [NBIT_WIDTH-1:0] nSymb,               // Computed nSymb
          output reg                  [3:0] remainderOut,        // This should be less than 10
          output reg                        divDone_p            // Indicates the completion of the division

		);


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

reg                   started;
reg             [3:0] cnt;
reg  [NBIT_WIDTH+5:0] remainder;         // Remainder


`ifndef RW_TXTIME_DIVIDER_ONECYCLE
reg  [NBIT_WIDTH+5:0] intRemainder;
reg  [NBIT_WIDTH+2:0] intnSymb;
wire [NBIT_WIDTH-1:0] roundUpExt;
`endif // RW_TXTIME_DIVIDER_ONECYCLE

reg  [NBITPSYMB_WIDTH+13:0] extnBitPSymb;

wire [NBITPSYMB_WIDTH-1:0] remainderTest;
wire                       oneMoreRound;
wire      [NBIT_WIDTH-1:0] nSymbLast;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    started       <= 1'd0;
  else 
  begin
    if (startDiv_p)
      started <= 1'd1;
    else if (started && (cnt == 4'd0))
      started <= 1'd0;
  end
end


`ifdef RW_TXTIME_DIVIDER_ONECYCLE
assign oneMoreRound    = (remainder[NBITPSYMB_WIDTH-1:0] >= nBitPSymb);
assign remainderTest   = (oneMoreRound) ? remainder[NBITPSYMB_WIDTH-1:0] - nBitPSymb : remainder[NBITPSYMB_WIDTH-1:0];
assign nSymbLast       = nSymb + {{{NBIT_WIDTH-1}{1'b0}},oneMoreRound};

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    cnt             <= 4'd15;
    remainder       <= {{NBIT_WIDTH+6}{1'b0}};
    divDone_p       <= 1'b0;
    nSymb           <= {{NBIT_WIDTH}{1'b0}}; 
    extnBitPSymb    <= {{NBITPSYMB_WIDTH+14}{1'b0}};
    remainderOut    <= 4'd0; 
  end  
  else 
  begin
    divDone_p  <= 1'b0;
    if (startDiv_p)
    begin
      nSymb           <= {{NBIT_WIDTH}{1'b0}}; 
      cnt             <= initCnt;
      remainder       <= {6'b0,nBit[NBIT_WIDTH-1:0]};
      remainderOut    <= 4'd0;
      if(initCnt == 4'd5)
        extnBitPSymb <= {10'b0,nBitPSymb,4'b0};  // Extension of the number of Bit per Symbole
      else
        extnBitPSymb <= {nBitPSymb,14'b0};  // Extension of the number of Bit per Symbole
    end
    if (started)
    begin
      //varnBitPSymb <=  extnBitPSymb<<cnt;
      if (cnt == 4'd0) 
      begin
        divDone_p <= 1'b1;
        remainderOut <= remainderTest[3:0];

        if (remainderTest > {{NBITPSYMB_WIDTH}{1'b0}})
        begin
          nSymb <= nSymbLast + {{{NBIT_WIDTH-1}{1'b0}},roundUp};
        end
        else
        begin
           nSymb <= nSymbLast;
        end
      end
      else if (remainder > {1'b0,extnBitPSymb})
        begin
          remainder <= remainder - {1'b0,extnBitPSymb};
          nSymb <= {nSymb[NBIT_WIDTH-2:0], 1'b1};
        end
      else
      begin
        nSymb <=  {nSymb[NBIT_WIDTH-2:0], 1'b0};
      end
      extnBitPSymb <=  {1'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:1]}; // extnBitPSymb>>1;
      cnt <= cnt - 4'b1;
    end
  end
end
`endif // RW_TXTIME_DIVIDER_ONECYCLE

`ifdef RW_TXTIME_DIVIDER_FIVECYCLE
always @ *
begin
  intRemainder = remainder;
  intnSymb  = {3'b0,nSymb};
  // First step
  if (intRemainder >= (extnBitPSymb))
  begin
    intRemainder = intRemainder - (extnBitPSymb);
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b1};
  end
  else
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b0};
  
  // Second step
  if (intRemainder >= {1'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:1]}) // intRemainder >= (extnBitPSymb>>1))
  begin
    intRemainder = intRemainder - {1'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:1]};//(extnBitPSymb>>1);
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b1};
  end
  else
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b0};

  // Third step
  if (intRemainder >= {2'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:2]}) // intRemainder >= (extnBitPSymb>>2))
  begin
    intRemainder = intRemainder - {2'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:2]};//(extnBitPSymb>>2);
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b1};
  end
  else
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b0};

  // Fourth step
  if (intRemainder >= {3'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:3]})//  intRemainder >= (extnBitPSymb>>3))
  begin
    intRemainder = intRemainder - {3'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:3]};//(extnBitPSymb>>3);
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b1};
  end
  else
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b0};
    
  // Fifth step
  if (intRemainder >= {4'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:4]})//  intRemainder >= (extnBitPSymb>>4))
  begin
    intRemainder = intRemainder - {4'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:4]};//(extnBitPSymb>>4);
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b1};
  end
  else
    intnSymb = {intnSymb[NBIT_WIDTH+1:0], 1'b0};
end
assign roundUpExt = {{{NBIT_WIDTH-1}{1'b0}},roundUp};
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    cnt           <= 4'd15;
    remainder     <= {{NBIT_WIDTH+6}{1'b0}}; 
    remainderOut  <= 4'd0;
    divDone_p     <= 1'd0;
    nSymb         <= {{NBIT_WIDTH}{1'b0}};
    extnBitPSymb  <= {{NBITPSYMB_WIDTH+14}{1'b0}};
  end  
  else 
  begin
    divDone_p  <= 1'd0;
    if (startDiv_p)
    begin
      nSymb        <= {{NBIT_WIDTH}{1'b0}};
      cnt          <= initCnt;
      remainder    <= {6'b0,nBit[NBIT_WIDTH-1:0]};
      remainderOut <= 4'd0;
      if (initCnt == 4'd5)
        extnBitPSymb <= {10'b0,nBitPSymb,4'b0};
      else
        extnBitPSymb <= {nBitPSymb,14'b0};
        
    end
    if (started)
    begin

      remainder    <= intRemainder;
      nSymb        <= intnSymb[NBIT_WIDTH-1:0] ;
      extnBitPSymb <= {5'd0,extnBitPSymb[NBITPSYMB_WIDTH+13:5]};//extnBitPSymb>>5; !!!
      
      cnt <= cnt - 4'd5;
      if (cnt == 4'd0)
      begin
        divDone_p <= 1'd1;
        remainderOut <= remainder[3:0];
        if (remainder > {{NBIT_WIDTH+6}{1'b0}})
//           nSymb <= nSymb + roundUp;
          nSymb <= nSymb + roundUpExt;
        else  
          nSymb <= nSymb;
      end
    end
  end
end
`endif // RW_TXTIME_DIVIDER_FIVECYCLE

endmodule
                 
