//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: rblanc $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 16829 $
// $Date: 2014-11-17 09:58:41 +0100 (Mon, 17 Nov 2014) $
// ---------------------------------------------------------------------------
// Dependencies     : None                                                      
// Description      : 
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
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module txBufferWepTkip(
  //$port_g Clock and Reset
  input  wire                 macCoreClk,           // Buffer Clock
  input  wire                 macCoreClkHardRst_n,  // Hard Reset
  input  wire                 macCoreClkSoftRst_n,  // Soft Reset

  //$port_g Tx Controller
  input  wire           [7:0] txPlainData,          // data from tx controller formatMPDU
  input  wire                 txPlainDataValid,     // data valid from tx controller formatMPDU
  input  wire                 txPlainDataEnd,       // data end from tx controller formatMPDU
  output wire                 txBufferNextFull,     // Indicate to tx controller formatMPDU that no more pop from txfifo
  
  //$port_g Wep Tkip interface
  input  wire                 txCsIsIdle,           // tx FSM is idle
  input  wire           [2:0] cipherType,           // indicate WEP / TKIP
  input  wire                 initDone_p,           // inidcate SBOX init done
  input  wire                 prnOutValid_p,        // indicate RC4 byte processeing done
  input  wire                 txFcsBusy,            // indicate FCS buffer is busy no more pop from txfifo

  output reg            [7:0] txPlainDataOut,       // data to RC4 cipher
  output wire                 prnStrobe_p,          // indicate pushing data to RC4
  output wire                 icvEnable_p_tx,       // indicate the data is applied to icv processing
  output reg                  icvSDrain_p           // start poping icv
 );

   reg [15:0]  txBuffer;          // 2 bytes buffers
   reg  [1:0]  txBufferEnd;       // memorize where is the last payload byte
   reg  [1:0]  txBufferCnt;       // counter used to manage buffer

   reg         txFcsBusy_ff1;     // delayed 1 cycle of fcs busy
   reg         firstPrnStrobe;    // detect the first payload byte
   reg         bufferEn;          // Enable buffer processing

   reg         prnStrobe_p_int;   // generation of the prnStrobe_p to push and get byte from RC4
   reg         noPrnOutValid;     // gating signal for prnStrobe_p_int
   
   wire        txBufferFull;      // buffer full
   wire        txBufferEmpty;     // buffer empty

   // Push and pop byte from RC4 only if not FCS busy
   assign      prnStrobe_p      = (prnStrobe_p_int == 1'b1) && (txFcsBusy == 1'b0);

   // Full and Empty flag
   assign      txBufferEmpty    = (txBufferCnt == 2'h0);
   assign      txBufferFull     = (txBufferCnt == 2'h2);
   assign      txBufferNextFull = ((txBufferCnt == 2'h1) && (txPlainDataValid == 1'b1) && (prnStrobe_p == 1'b0)) || (txBufferCnt == 2'h2);   

   // Generation of icvEnable_p_tx
   assign      icvEnable_p_tx   = (bufferEn    == 1'b1) ? prnStrobe_p : txPlainDataValid;

   always @(posedge macCoreClk, negedge macCoreClkHardRst_n)
   begin
     if(macCoreClkHardRst_n == 1'b0)
     begin
       txBuffer         <= 16'h0;
       txBufferEnd      <=  2'h0;
       txBufferCnt      <=  2'h0;
       txFcsBusy_ff1    <=  1'h0;
       firstPrnStrobe   <=  1'h0;
       txPlainDataOut   <=  8'h0;
       prnStrobe_p_int  <=  1'h0;
       icvSDrain_p      <=  1'h0;
       bufferEn         <=  1'h0;
       noPrnOutValid    <=  1'h0;
     end
     else if(macCoreClkSoftRst_n == 1'b0)
     begin
       txBuffer         <= 16'h0;
       txBufferEnd      <=  2'h0;
       txBufferCnt      <=  2'h0;
       txFcsBusy_ff1    <=  1'h0;
       firstPrnStrobe   <=  1'h0;
       txPlainDataOut   <=  8'h0;
       prnStrobe_p_int  <=  1'h0;
       icvSDrain_p      <=  1'h0;
       bufferEn         <=  1'h0;
       noPrnOutValid    <=  1'h0;
     end
     else
     begin
       // Delay signal of FCS Busy
       txFcsBusy_ff1 <=  txFcsBusy;
  
       // When initDone_p and the ctype is WEP / TKIP then enable buffer and reset others registers
       if((initDone_p == 1'b1) && ((cipherType == 3'h1) || (cipherType == 3'h2)))
       begin
         txBuffer         <= 16'h0;
         txBufferEnd      <=  2'h0;
         txBufferCnt      <=  2'h0;
         txFcsBusy_ff1    <=  1'h0;
         firstPrnStrobe   <=  1'h0;
         txPlainDataOut   <=  8'h0;
         prnStrobe_p_int  <=  1'h0;
         icvSDrain_p      <=  1'h0;
         bufferEn         <=  1'h1;
         noPrnOutValid    <=  1'h0;
       end

       // bufferEn is reset when txCsIsIdle
       if(txCsIsIdle)
       begin
         bufferEn <= 1'h0;
       end

       // When bufferEn then start processing
       if(bufferEn == 1'b1)
       begin
         // Capturing plain data into the right buffer according to 
         // txBufferFull txBufferEmpty txPlainDataValid prnStrobe_p txBufferCnt
         // thus allow to have read and write into the buffer at the same time.
         if((txBufferFull == 1'b0) && (txPlainDataValid == 1'b1) && (prnStrobe_p == 1'b0))
         begin
           case(txBufferCnt)
             2'h0    :
             begin
               txBufferEnd[0]  <= txPlainDataEnd;
               txBuffer[7:0]   <= txPlainData;
             end
             2'h1    :
             begin
               txBufferEnd[1]  <= txPlainDataEnd;
               txBuffer[15:8]  <= txPlainData;
             end
             default : 
             begin
               txBufferEnd <= txBufferEnd;
               txBuffer    <= txBuffer;
             end
           endcase
         end
         else if((txBufferEmpty == 1'b0) && (txPlainDataValid == 1'b0) && (prnStrobe_p == 1'b1))
         begin
           txBufferEnd  <= {1'b0,txBufferEnd[1]};
           txBuffer     <= {8'h0,txBuffer[15:8]};
         end
         else if((txPlainDataValid == 1'b1) && (prnStrobe_p == 1'b1))
         begin
           case(txBufferCnt)
             2'h1    :
             begin
               txBufferEnd[0]  <= txPlainDataEnd;
               txBuffer[7:0]   <= txPlainData;
             end
             2'h2    :
             begin
               txBufferEnd[0]  <= txBufferEnd[1];
               txBuffer[7:0]   <= txBuffer[15:8];
               txBufferEnd[1]  <= txPlainDataEnd;
               txBuffer[15:8]  <= txPlainData;
             end
             default : 
             begin
               txBufferEnd <= txBufferEnd;
               txBuffer    <= txBuffer;
             end
           endcase
         end     

         // Counter management
         if((txBufferFull == 1'b0) && (txPlainDataValid == 1'b1) && (prnStrobe_p == 1'b0))
         begin
           txBufferCnt <= txBufferCnt + 2'h1;
         end
         else if((txBufferEmpty == 1'b0) && (txPlainDataValid == 1'b0) && (prnStrobe_p == 1'b1))
         begin
           txBufferCnt <= txBufferCnt + 2'h3; // as like as txBufferCnt <= txBufferCnt - 2'h1
         end

         // first strobe in the buffer flag
         if((txPlainDataValid == 1'b1) && (txBufferEmpty == 1'b0))
         begin
           firstPrnStrobe <= 1'b1;
         end
         else if((txPlainDataValid == 1'b1) && (txBufferEmpty == 1'b1))
         begin
           firstPrnStrobe <= 1'b0;
         end

         // noPrnOutValid used to mask the prnStrobe_p_int generation
         if(prnStrobe_p == 1'b1)
         begin
           noPrnOutValid    <= 1'b1;
         end
         else if(prnOutValid_p) //TBD: Very bad condition since no resync on prnOutValid_p (signal from counter on another clock domain)
         begin
           noPrnOutValid    <= 1'b0;
         end
  
         // push the byte to the RC4 when :
         // If buffer is not empty and data is comming
         // If buffer is not empty and RC4 previous byte done
         // If FCS was busy and buffer is not empty and RC4 previous byte done
         if( ((txPlainDataValid == 1'b1) && (firstPrnStrobe == 1'b0) && (txBufferEmpty == 1'b0)) ||
             ((prnOutValid_p    == 1'b1) && (txFcsBusy      == 1'b0) && (txBufferEmpty == 1'b0)) ||
             ((txFcsBusy_ff1    == 1'b1) && (txFcsBusy      == 1'b0) && (txBufferEmpty == 1'b0) && ((noPrnOutValid == 1'b0) || (prnOutValid_p == 1'b1))))
         begin
           prnStrobe_p_int  <= 1'b1;
           txPlainDataOut   <= txBuffer[7:0];
           icvSDrain_p      <= txBufferEnd[0];
         end
         else if(prnStrobe_p_int == 1'b1)
         begin
           prnStrobe_p_int  <= 1'b0;
           icvSDrain_p      <= 1'b0;
         end
       end
     end
   end

endmodule

//------------------- END OF FILE ----------------//
