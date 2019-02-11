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
// Description      : Fifo Controller module.
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

module rxFifoController #(parameter ADDRWIDTH = 6,DEPTH=64) (
          //$port_g Clock and Reset of write interface
          input wire                      wrClk ,             // Write Clock
          input wire                      wrHardReset_n ,     // Write Asynchronous reset

          //$port_g Clock and Reset of read interface
          input wire                      rdClk ,             // Write Clock
          input wire                      rdHardReset_n ,     // Write Asynchronous reset

          //$port_g Write control interface
          input wire                      wrFlush ,           // Flush Request from wrClk clock domain
          input wire                      fifoWrite ,         // Write Access Request
          output wire                     fifoAlmostFull ,    // Indicates that the FIFO is almost full (on wrClk clock domain)
          output wire                     fifoFull ,          // Indicates that the FIFO is full (on wrClk clock domain)
          output wire                     fifoAlmEmptyWrClk , // Indicates that the FIFO is almost empty (on wrClk clock domain)
          output wire                     fifoEmptyWrClk ,    // Indicates that the FIFO is empty (on wrClk clock domain)
          output wire [(ADDRWIDTH - 1):0] fifoWrPtr ,         // Write Pointer
          output wire                     fifoPtrsNull ,      // Indicates that the both FIFO pointers are null (on wrClk clock domain)

          //$port_g Read control interface
          input wire                      rdFlush ,           // Flush Request from rdClk clock domain
          input wire                      fifoRead ,          // Read Access Request
          output wire                     fifoAlmEmpty,       // Indicates that the FIFO is almost empty (on rdClk clock domain)
          output wire                     fifoEmpty ,         // Indicates that the FIFO is empty (on rdClk clock domain)
          output wire [(ADDRWIDTH - 1):0] fifoRdPtr           // Read Pointer
          );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

localparam ALMOST_EMPTY_THRESHOLD = 8;
localparam ALMOST_FULL_THRESHOLD = 2;

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// Internal variables of the module ..
reg    [ADDRWIDTH:0] fifoWrAddr ;

`ifdef RW_SIMU_ON
reg    [ADDRWIDTH:0] filledCount ;
reg    [ADDRWIDTH:0] filledCountRd ;
`endif

// Internal variables of the module ..
wire   [ADDRWIDTH:0] fifoWrAddrGray ;
wire   [ADDRWIDTH:0] fifoWrAddrSync ;
wire   [ADDRWIDTH:0] fifoWrAddrGraySync ;
wire   [ADDRWIDTH:0] fifoRdAddr ;
wire   [ADDRWIDTH:0] fifoRdAddrGray ;
wire   [ADDRWIDTH:0] fifoRdAddrSync ;
wire   [ADDRWIDTH:0] fifoRdAddrGraySync ;
wire   [ADDRWIDTH:0] wrAddrAhead5 ; 



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
      gray2Binary[ADDRWIDTH - i] = gray2Binary[ADDRWIDTH - i+1] ^ gray[ADDRWIDTH - i] ;
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

// Maintains a pointer to 7th location from the current write pointer
// used for fifoAlmostFull logic
//assign wrAddrAhead5 = fifoWrAddr + 7 ;
assign wrAddrAhead5 = fifoWrAddr + ALMOST_FULL_THRESHOLD ;

// The status of fifoFull is continuously driven based on the 
// fifo addresses
assign fifoFull = (fifoWrAddr[(ADDRWIDTH-1):0] ==
                  fifoRdAddrSync[(ADDRWIDTH-1):0]) &
                  (fifoWrAddr[ADDRWIDTH] ^ fifoRdAddrSync[ADDRWIDTH]);

// fifoAlmostFull asserted when it is 1 word less than full
assign fifoAlmostFull = (wrAddrAhead5[(ADDRWIDTH-1):0] == 
                        fifoRdAddrSync[(ADDRWIDTH-1):0]) &
                        (wrAddrAhead5[ADDRWIDTH] ^ fifoRdAddrSync[ADDRWIDTH]);

// fifoEmpty is asserted in rdClk domain after synchronising the
// fifoWrAddr to rdClk. 

assign fifoEmpty = (fifoRdAddr == fifoWrAddrSync);

assign fifoAlmEmpty = ((fifoWrAddrSync >= fifoRdAddr) ? 
                      ((fifoWrAddrSync - fifoRdAddr) < ALMOST_EMPTY_THRESHOLD):
                      ((fifoRdAddr[(ADDRWIDTH-1):0] - 
                      fifoWrAddrSync[(ADDRWIDTH-1):0]) >= DEPTH - ALMOST_EMPTY_THRESHOLD));

// fifoEmpty syncronised to wrClk
syncLevel u_fifoEmpty (
                 .syncClk (wrClk) ,
                 .nSyncRst (wrHardReset_n) ,
                 .dataIn (fifoEmpty) ,
                 .dataOut (fifoEmptyWrClk)
                 );

assign fifoAlmEmptyWrClk = ((fifoWrAddr >= fifoRdAddrSync) ? 
                            ((fifoWrAddr - fifoRdAddrSync) < ALMOST_EMPTY_THRESHOLD):
                            ((fifoRdAddrSync[(ADDRWIDTH-1):0] - 
                            fifoWrAddr[(ADDRWIDTH-1):0]) >= DEPTH - ALMOST_EMPTY_THRESHOLD));

// fifoPtrsNull is asserted when both write and read pointers are null
assign fifoPtrsNull = (fifoWrAddr == fifoRdAddrSync) && (fifoWrAddr == {{ADDRWIDTH}{1'b0}});

// fifoRdAddrGray is syncronised to rdClk
// Following instantiation incremnets fifoRdAddr and
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
                             .syncHardRst_n (rdHardReset_n) ,
                             .dataIn (fifoRdAddrGray) ,
                             .dataOut (fifoRdAddrGraySync)
                             );

// fifoWrAddrGray is syncronised to rdClk
// Following instantiation incremnets fifoWrAddr and
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
                             .syncHardRst_n (wrHardReset_n) ,
                             .dataIn (fifoWrAddrGray) ,
                             .dataOut (fifoWrAddrGraySync)
                             );

// The fifoWrAddr is incremented on every fifoWrite.
always @(posedge wrClk or negedge wrHardReset_n) 
begin
   if(wrHardReset_n == 1'b0) 
     fifoWrAddr <= {(ADDRWIDTH+1){1'b0}}; 
   else if (wrFlush) 
     fifoWrAddr <= {(ADDRWIDTH+1){1'b0}}; 
   else if(fifoWrite && (fifoFull == 1'b0)) 
     fifoWrAddr <= fifoWrAddr + {{(ADDRWIDTH){1'b0}},1'b1};
   else 
     fifoWrAddr <= fifoWrAddr;
end

`ifdef RW_SIMU_ON
// Following logic constantly maintains the difference (in number
// of locations) between read and write address.
always @( fifoWrAddr or fifoRdAddrSync) 
begin
   if (fifoWrAddr[ADDRWIDTH] ^ fifoRdAddrSync[ADDRWIDTH] ) 
   begin
      filledCount = {1'b1, fifoWrAddr[(ADDRWIDTH-1):0]} - {1'b0, fifoRdAddrSync[(ADDRWIDTH-1):0]} ;
   end
   else 
     filledCount = fifoWrAddr - fifoRdAddrSync;
end

// Following logic constantly maintains the difference (in number
// of locations) between read and write address.
always @( fifoWrAddrSync or fifoRdAddr) 
begin
   if (fifoWrAddrSync[ADDRWIDTH] ^ fifoRdAddr[ADDRWIDTH] ) 
   begin
      filledCountRd = {1'b1, fifoWrAddrSync[(ADDRWIDTH-1):0]} - {1'b0, fifoRdAddr[(ADDRWIDTH-1):0]} ;
   end
   else 
     filledCountRd = fifoWrAddrSync - fifoRdAddr;
end
`endif

endmodule
                 
