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
// Description      : Controls the Tx part of the Phy interface
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

module TxStateCtl( 
         //$port_g clock and Reset                                                                
         input  wire        mpIFClk,                   // PHY clock                      
         input  wire        mpIFClkHardRst_n,          // PHY clock reset                
         input  wire        mpIFClkSoftRst_n,          // PHY clock soft reset
         input  wire        macCoreTxClk,              // mac core Tx clock              
         input  wire        macCoreClkHardRst_n,       // mac core Tx clock hard reset        

         //$port_g Tx  Controller If                                                            
         input  wire        startTx_p,                 // Start Tx trigger                   
         input  wire        stopTx_p,                  // Stop Tx trigger                    
         input  wire [ 7:0] txPwrLevel,                // Transmit Power Level             
         input  wire [ 1:0] chBW,                      // TX Vector Channel Bandwidth             
         input  wire [ 1:0] chOffset,                  // TX Vector transmit vector field              
         input  wire        smoothing,                 // TX Vector Smoothing recommended            
         input  wire [ 7:0] antennaSet,                // TX Vector Antenna Set           
         input  wire [ 7:0] smmIndex,                  // TX Vector Spatial Map Matrix Index           
         input  wire [ 6:0] mcs,                       // TX Vector Modulation Coding Scheme           
         input  wire        preType,                   // TX Vector Preamble Type         
         input  wire [ 2:0] formatMod,                 // TX Vector Format and Modulation           
         input  wire [ 1:0] numExtnSS,                 // TX Vector Number of Extension Spatial Streams              
         input  wire [ 1:0] stbc,                      // TX Vector Space Time Block Coding           
         input  wire        fecCoding,                 // TX Vector FEC Coding             
         input  wire        sounding,                  // TX Vector Indicates whether this PPDU is Sounding        
         input  wire [11:0] legLength,                 // TX Vector Legacy Length of the PPDU            
         input  wire [ 3:0] legRate,                   // TX Vector Legacy Rate of the PPDU               
         input  wire [15:0] service,                   // TX Vector Service              
         input  wire [19:0] htLength,                  // TX Vector Length of the HT and VHT PPDU              
         input  wire [ 2:0] nTx,                       // TX Vector Number of Transmit Chains.      
         input  wire [ 2:0] nSTS,                      // TX Vector Indicates the number of space-time streams.
         input  wire        shortGI,                   // TX Vector Short Guard Interval              
         input  wire        aggreation,                // TX Vector MPDU Aggregate
         input  wire        beamFormed,                // TX Vector BeamFormed
         input  wire        disambiguityBit,           // TX Vector Disambiguity
         input  wire [8:0]  partialAID,                // TX Vector partial AID
         input  wire [5:0]  groupID,                   // TX Vector group ID
         input  wire        dozeNotAllowed,            // TX Vector TXOP PS Not Allowed
         input  wire        continuousTx,              // TX Vector continuous transmit 
         //
         output wire        mpIfTxErr_p,               // indicate a phy error to Tx controller         

         //$port_g Phy If                                                                            
         input  wire        phyRdy,                    // data valid signal                  
         input  wire        txEnd_p,                   // data enable                        
         input  wire        phyErr_p,                  // phy error                          
         //                                                                              
         output reg         txReq,                     // Tx request                         
         output wire [ 7:0] txData,                    // Tx data
         output reg         macDataValid,              // Tx data valid                            

         //$port_g registers
         input  wire        macPHYIFFIFOReset,         // Flush the FIFO
         input  wire        rateControllerMPIF,        // select transmit mechanism
                                                       // 0 reverse handshaking
                                                       // 1 phy strobe
         
         //$port_g FIFO Interface
         input  wire [ 7:0] mpIfTxFifoDataout,         // Tx FIFO input
         input  wire        mpIfTxFifoEmtpy,           // Tx FIFO empty
         //
         output reg         mpIfFifoReadEn,            // Read enable
         output reg         txFifoRdClkFlush,          // flush FIFO
         
         //$port_g Keep RF
         input  wire        mackeepRFOn,               // input Keep RF
         //
         output reg         TxkeepRFOn,                // output Keep RF
         
         output reg         mpifUnderRun               // underrun
         );

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
//$fsm_sd rxstate
localparam
                 IDLE  =  2'd0,  // 
            TX_VECTOR  =  2'd1,  // 
              TX_DATA  =  2'd2,  // 
               TX_END  =  2'd3;  // 

//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
// txstate FSM signals definition
reg [1:0] txstateCs;              // txstate FSM Current State
reg [1:0] txstateNs;              // txstate FSM Next State
  
reg [4:0] txVectorCnt;            // Tx vector counter

reg [7:0] txVector;               // formatted tx vector


wire      fifo_reset;             // fifo reset from registers

reg       phyRdy_reg;             // registered phyRdy
reg [7:0] continuousTxData;
reg       stopTxFlg;             // Memorize the pulse stopTx_p when it happended in TX_VECTOR state

`ifdef RW_SIMU_ON
  // String definition to dislpay txstate current state
  reg [9*8:0] txstateCs_str;
`endif // RW_SIMU_ON



//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign txData = (txstateCs == TX_VECTOR) ? txVector : (continuousTx) ? continuousTxData : mpIfTxFifoDataout;


always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    continuousTxData <= 8'b0; 
  else if(continuousTx && phyRdy_reg)
    continuousTxData <= continuousTxData + 8'b1; 
end

always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    stopTxFlg <= 1'b0;
  else if((mpIFClkSoftRst_n == 1'b0) || (txstateCs == TX_END) || startTx_p)
    stopTxFlg <= 1'b0;
  else if((stopTx_p) && (txstateCs == TX_VECTOR))
    stopTxFlg <= 1'b1; 
end


pulse2PulseSynchro U_stoptTx_p_synchro (
                .srcclk (mpIFClk),
                .srcresetn (mpIFClkHardRst_n),
                .dstclk (macCoreTxClk),
                .dstresetn (macCoreClkHardRst_n),
                .srcdata (phyErr_p),
                .dstdata (mpIfTxErr_p)
                );

pulse2PulseSynchro U_fiforeset_synchro (
                .srcclk (macCoreTxClk),
                .srcresetn (macCoreClkHardRst_n),
                .dstclk (mpIFClk),
                .dstresetn (mpIFClkHardRst_n),
                .srcdata (macPHYIFFIFOReset),
                .dstdata (fifo_reset)
                );

// txstate FSM Current State Logic 
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    txstateCs <= IDLE; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    txstateCs <= IDLE; 
  else
    txstateCs <= txstateNs; 
end


// txstate FSM Next State Logic.
always @* 
begin
  case(txstateCs)

    IDLE:
      //$fsm_s In IDLE state, the state machine waits for a Transmit transaction 
      if (startTx_p) 
        //$fsm_t When startTx_p is true, the state machine goes to TX_VECTOR state
        txstateNs = TX_VECTOR; 
      else
        txstateNs = txstateCs;

    TX_VECTOR:
      //$fsm_s In TX_VECTOR state, the state machine waits for the end of  
      // the vector transmission or for an abort
      if (txVectorCnt == 5'd20)
      begin
        if(stopTxFlg || stopTx_p)
          //$fsm_t When the is a MAC aborted durring the TX_VECTOR, the state machine goes to TX_END state at the end of TX_VECTOR
          txstateNs = TX_END;
        else
          //$fsm_t When txVector is 0d14, the Tx vectors state ends and the state machine 
          // goes to TX_DATA state
          txstateNs = TX_DATA;
      end
      else if (phyErr_p)
        //$fsm_t When the is a MAC or a PHY abort, the state machine goes to TX_END state
        txstateNs = TX_END;
      else
        txstateNs = txstateCs;

    TX_DATA:
      //$fsm_s In TX_DATA state, the state machine waits for the end of transmission 
      if (txEnd_p == 1'b1)
        //$fsm_t When txend is true, the state machine goes to IDLE state
        txstateNs = IDLE; 
      else if (stopTx_p || phyErr_p)
        //$fsm_t When stopTx_p or phyErr_p occurs, the state machine goes to TX_END state
        txstateNs = TX_END;
      else
        txstateNs = txstateCs;

    TX_END:
      //$fsm_s In TX_END state, the state machine waits for the tx end signal
      // from the phy
      if (txEnd_p) 
        //$fsm_t When txend is true, the state machine goes to IDLE state
        txstateNs = IDLE; 
      else
        txstateNs = txstateCs;
    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:
      txstateNs = IDLE; 
    // pragma coverage block = on 
   endcase
end

// tx vector counter
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    txVectorCnt <= 5'b0000; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    txVectorCnt <= 5'b0000; 
  // increment vector count each time a vector is sampled 
  // byt the rx FIFO
  else if ( txstateCs == TX_VECTOR ) 
    txVectorCnt <= txVectorCnt + 5'd1; 
  else
    txVectorCnt  <= 5'b0000; 
end


// control interface
// Tx Vectors
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    txVector     <= 8'b00000000; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    txVector     <= 8'b00000000; 
  else 
  begin
     if (txstateCs  == TX_VECTOR)
     begin
       case(txVectorCnt)
         5'd0:
//           txVector <= {smoothing,chOffset,1'b0,chBW,txPwrLevel};
           txVector <= txPwrLevel;
         5'd1:
           txVector <= {chBW,1'b0,continuousTx,smoothing,1'b0,fecCoding,sounding};
         5'd2:
           txVector <= antennaSet;
         5'd3:
           txVector <= smmIndex;
         5'd4:
           txVector <= {preType,mcs};
         5'd5:
           txVector <= {nSTS,numExtnSS,formatMod};
         5'd6:
           txVector <= legLength[7:0];
         5'd7:
           txVector <= {legRate,legLength[11:8]};
         5'd8:
           txVector <= service[7:0];
         5'd9:
           txVector <= service[15:8];
         5'd10:
           txVector <= htLength[ 7:0];
         5'd11:
           txVector <= htLength[15:8];
         5'd12:
           txVector <= {disambiguityBit,shortGI,dozeNotAllowed,aggreation,htLength[19:16]};
         5'd13:
           txVector <= {1'b0,beamFormed,stbc,1'b0,nTx};
         5'd14:
           txVector <= partialAID[7:0];
         5'd15:
           txVector <= {1'b0,groupID,partialAID[8]};
         default:
           txVector <= 8'b00000000; 
       endcase
     end
     else
      txVector     <= 8'b00000000;  
  end
end

// control interface
// Mac Data valid and FIFO flush
// keepRfon latch
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    macDataValid     <= 1'b0;
    txFifoRdClkFlush <= 1'b0;
    txReq            <= 1'b0;
    TxkeepRFOn       <= 1'b0;
   end
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    macDataValid     <= 1'b0;
    txFifoRdClkFlush <= 1'b0;
    txReq            <= 1'b0;
    TxkeepRFOn       <= 1'b0;
   end
  else 
  begin
    // Sample TxkeeRFOn only when TxReq is asserted
    if (txReq)
      TxkeepRFOn <= mackeepRFOn;
    
    // when the State Machine is not idle, assert Tx Req
    if (txstateCs == TX_VECTOR) 
      txReq            <= 1'b1;
    else if (txEnd_p || stopTx_p || stopTxFlg || (txstateCs == IDLE))
      txReq            <= 1'b0;
    
    // flush in case of external flush, abort of return to idle
    if  ((fifo_reset) || (txstateCs  == TX_END) || 
         ((txstateCs  == TX_DATA) && (txstateNs  == IDLE)))
      txFifoRdClkFlush <= 1'b1;
    else   
      txFifoRdClkFlush <= 1'b0;
    
    // generate MAC data valid only if a Read as been done
    if  (txstateCs  == TX_DATA)    
    begin
      if ( mpIfFifoReadEn == 1'b1)
        macDataValid    <= 1'b1; 
      else
        macDataValid    <= 1'b0;          
    end
    else
    begin
      macDataValid     <= 1'b0;   
    end
  end
end


// Phy Ready register
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    phyRdy_reg <= 1'b0; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    phyRdy_reg <= 1'b0; 
  else
    phyRdy_reg <= phyRdy; 
end

// Generate FIFO read enable
always @*
begin
  if  (txstateCs  == TX_DATA)    
  begin
    if (phyRdy_reg && (!mpIfTxFifoEmtpy || continuousTx))
      mpIfFifoReadEn = 1'b1;
    else
      mpIfFifoReadEn = 1'b0;
  end
  else
  begin
    mpIfFifoReadEn   = 1'b0;   
  end
end


// UnderRun detection
always @ (posedge mpIFClk or negedge mpIFClkHardRst_n) 
begin
  if (mpIFClkHardRst_n == 1'b0)  // Asynchronous Reset
    mpifUnderRun             <= 1'b0; 
  else if (mpIFClkSoftRst_n == 1'b0)  // Synchronous Reset
    mpifUnderRun             <= 1'b0; 
  else 
  begin
    if (txstateCs != IDLE)
      // Violation if the FIFO handling
      // assert underRun
      if (phyRdy_reg && (mpIfTxFifoEmtpy && !continuousTx))
        mpifUnderRun  <= 1'b1; 
      else
        mpifUnderRun  <= mpifUnderRun; 
        
    else
      mpifUnderRun    <= 1'b0; 
  end
end


`ifdef RW_SIMU_ON
// txstate FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (txstateCs)
                 IDLE  :  txstateCs_str = {"IDLE"};
            TX_VECTOR  :  txstateCs_str = {"TX_VECTOR"};
              TX_DATA  :  txstateCs_str = {"TX_DATA"};
               TX_END  :  txstateCs_str = {"TX_END"};
   endcase
end
`endif // RW_SIMU_ON
endmodule
                 
