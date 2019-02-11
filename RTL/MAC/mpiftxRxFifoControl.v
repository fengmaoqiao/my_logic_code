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
// Description      : 
//     The read and write pointers for transmit FIFO are controlled here.
//     Also the FIFO status such as, full, empty, 
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

module mpiftxRxFifoControl #(parameter ADDRWIDTH = 4)(
          //$port_g Inputs are defined here..
          input  wire                       wrClk ,           // Write clock     
          input  wire                       wrHardReset_n ,   // Write clock hard reset         
          input  wire                       rdClk ,           // Read clock     
          input  wire                       rdHardReset_n ,   // Read clock hard reset
          input  wire                       rdFlush ,         // Read Flush     
          input  wire                       fifoWrite ,       // Write enables     
          input  wire                       fifoRead ,        // Read enable     

          //$port_g Outputs defined here ..
          output wire   [(ADDRWIDTH - 1):0] fifoWrPtr ,       // Write ptr
          output wire   [(ADDRWIDTH - 1):0] fifoRdPtr ,       // Read ptr
          output wire                       fifoFull ,        // fifo full indicator
          output wire                       fifoEmpty ,       // fifo empty indicator
          output wire                       fifoPtrsNull      // Indicates FIFO pointers null
          );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// Output types defined here ..
// Internal variables of the module ..
reg    [ADDRWIDTH:0] fifoWrAddr ;

// Internal variables of the module ..
wire   [ADDRWIDTH:0] fifoWrAddrGray ;
wire   [ADDRWIDTH:0] fifoWrAddrSync ;
wire   [ADDRWIDTH:0] fifoWrAddrGraySync ;
wire   [ADDRWIDTH:0] fifoRdAddr ;
wire   [ADDRWIDTH:0] fifoRdAddrGray ;
wire   [ADDRWIDTH:0] fifoRdAddrSync ;
wire   [ADDRWIDTH:0] fifoRdAddrGraySync ;

wire                 wrFlush ;      
wire                 rdFlushDly ;      
reg                  rdFlushDly2 ;      
reg                  rdFlushDly3 ;      
wire                 rdFlushInt;

reg                  flushOnGoing;

`ifdef RW_SIMU_ON
integer fifoCnt;
`endif // RW_SIMU_ON

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////
// This function converts Gray Code into Binary Code
function [ADDRWIDTH:0] gray2Binary ;
input    [ADDRWIDTH:0] gray ;
integer i ;
begin
   gray2Binary[ADDRWIDTH] = gray[ADDRWIDTH] ;
   for(i = 1; i <= ADDRWIDTH; i = i + 1) 
   begin
      gray2Binary[ADDRWIDTH - i] =
           gray2Binary[ADDRWIDTH - i+1] ^ gray[ADDRWIDTH - i] ;
   end
end
endfunction

// fifoRdAddrGray converted to binary
assign fifoRdAddr = gray2Binary(fifoRdAddrGray) ;

// Gray to Binary conversion for the synchronised Read Address
assign fifoRdAddrSync = gray2Binary(fifoRdAddrGraySync) ;

// Gray to Binary conversion for the synchronised Write Address
assign fifoWrAddrSync = gray2Binary(fifoWrAddrGraySync) ;

// The MSB of the address is not used as a part of Pointer.
//fifoWrPtr
assign fifoWrPtr  = fifoWrAddr[(ADDRWIDTH-1):0] ;
//fifoRdPtr
assign fifoRdPtr  = fifoRdAddr[(ADDRWIDTH-1):0] ;

// The status of fifoFull is continuously driven based on the 
// fifo addresses
assign fifoFull = (fifoWrAddr[(ADDRWIDTH-1):0] == fifoRdAddrSync[(ADDRWIDTH-1):0]) &&
                  (fifoWrAddr[ADDRWIDTH] ^ fifoRdAddrSync[ADDRWIDTH]);

// fifoEmpty is asserted in rdClk domain after synchronising the
// fifoWrAddr to rdClk. 
assign fifoEmpty = (fifoRdAddr == fifoWrAddrSync) || flushOnGoing || rdFlush;

// fifoPtrsNull is asserted when both write and read pointers are null
assign fifoPtrsNull = (fifoRdAddr == fifoWrAddrSync) && (fifoWrAddrSync == {(ADDRWIDTH+1){1'b0}});

// fifoRdAddrGray is synchronised to rdClk
// Following instantiation increments fifoRdAddr and
// converts this new address into corresponding Gray encoding
fifoPtrGray #(.ADDRWIDTH(ADDRWIDTH)) u_fifoRdAddrGray(
                             .clk(rdClk),
                             .hardReset_n(rdHardReset_n),
                             .flush(rdFlush),
                             .rdWrEn(fifoRead),
                             .rdWrDisable(fifoEmpty),
                             .fifoAddr(fifoRdAddr),
                             .fifoAddrGray(fifoRdAddrGray)
                            );

// fifoRdAddrGray is synchronised to wrClk
syncBus #(.SYNC_WIDTH(ADDRWIDTH)) u_fifoRdAddrSync (
                             .syncClk (wrClk) ,
                             .syncHardRst_n (wrHardReset_n) ,
                             .dataIn (fifoRdAddrGray) ,
                             .dataOut (fifoRdAddrGraySync)
                             );

// fifoWrAddrGray is syncronised to rdClk
// Following instantiation increments fifoWrAddr and
// converts this new address into corresponding Gray encoding
fifoPtrGray #(.ADDRWIDTH(ADDRWIDTH)) u_fifoWrAddrGray(
                             .clk(wrClk),
                             .hardReset_n(wrHardReset_n),
                             .flush(wrFlush),
                             .rdWrEn(fifoWrite),
                             .rdWrDisable(fifoFull),
                             .fifoAddr(fifoWrAddr),
                             .fifoAddrGray(fifoWrAddrGray)
                            );

// fifoWrAddrGray is synchronised to rdClk
syncBus #(.SYNC_WIDTH(ADDRWIDTH)) u_fifoWrAddrSync (
                             .syncClk (rdClk) ,
                             .syncHardRst_n (rdHardReset_n) ,
                             .dataIn (fifoWrAddrGray) ,
                             .dataOut (fifoWrAddrGraySync)
                             );


// Generation of wrFlush 
pulse2PulseSynchro U_wrFlush_synchro (
                .srcclk (rdClk),
                .srcresetn (rdHardReset_n),
                .dstclk (wrClk),
                .dstresetn (wrHardReset_n),
                .srcdata (rdFlushInt),
                .dstdata (wrFlush)
                );

pulse2PulseSynchro U_rdFlushDly_synchro (
                .srcclk (wrClk),
                .srcresetn (wrHardReset_n),
                .dstclk (rdClk),
                .dstresetn (rdHardReset_n),
                .srcdata (wrFlush),
                .dstdata (rdFlushDly)
                );
                

// Generation of flushOnGoing flag indicating that the FIFO is being flushed.
// It allows to keep the fifo empty flag set during the flush process.
always @(posedge rdClk or negedge rdHardReset_n) 
begin
   if (rdHardReset_n == 1'b0) 
     flushOnGoing <= 1'b0; 
   else if (rdFlushDly) 
     flushOnGoing <= 1'b0; 
   else if(rdFlushInt) 
     flushOnGoing <= 1'b1; 
end


always @(posedge rdClk or negedge rdHardReset_n) 
begin
   if (rdHardReset_n == 1'b0) 
   begin
     rdFlushDly2 <= 1'b0; 
     rdFlushDly3 <= 1'b0; 
   end
   else
   begin
     rdFlushDly2 <= rdFlushDly; 
     rdFlushDly3 <= rdFlushDly2; 
   end  
end

assign rdFlushInt =  rdFlush && !flushOnGoing && !rdFlushDly && !rdFlushDly3 && !rdFlushDly2;


// The fifoWrAddr is incrmented on every fifoWrite.
always @(posedge wrClk or negedge wrHardReset_n) 
begin
   if (wrHardReset_n == 1'b0) 
     fifoWrAddr <= {(ADDRWIDTH+1){1'b0}}; 
   else if (wrFlush) 
     fifoWrAddr <= {(ADDRWIDTH+1){1'b0}}; 
   else if(fifoWrite && (fifoFull == 1'b0)) 
     fifoWrAddr <= fifoWrAddr + {{(ADDRWIDTH){1'b0}},1'd1};
   else 
     fifoWrAddr <= fifoWrAddr;
end


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON

always @(posedge wrClk or negedge wrHardReset_n) 
begin
   if(wrHardReset_n == 1'b0) 
     fifoCnt = 0; 
   else if (wrFlush) 
     fifoCnt = 0; 
   else if(fifoWrite && (fifoFull == 1'b0)) 
     fifoCnt = fifoCnt + 1; 
end

always @(posedge rdClk or negedge rdHardReset_n) 
begin
   if(rdHardReset_n == 1'b0) 
     fifoCnt = 0; 
   else if (wrFlush) 
     fifoCnt = 0; 
   else if(fifoRead && (fifoEmpty == 1'b0)) 
     fifoCnt = fifoCnt - 1; 
end


`endif // RW_SIMU_ON
endmodule
//---------- END OF FILE ----------
