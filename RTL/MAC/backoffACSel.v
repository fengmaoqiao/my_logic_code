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

module backoffACSel( 
            //$port_g Clock and Reset
            input  wire            macCoreClk,               // mac core clock      
            input  wire            macCoreClkHardRst_n,      // mac core clock reset

            input  wire            macCoreClkSoftRst_n,      // MAC core clock soft reset
            
            //$port_g MAC Controller interface
            input  wire            bcnRcved_p,               // Beacon received
            
            //$port_g Tx controller interface
            input  wire  [15:0]    acMOT,                    // Current AC Medium Occupancy timer
            input  wire            retryType,                // Indicates the type of retry
            input  wire            retry_p,                  // Indicates that the current frame has to be retried
            input  wire            txSuccessful_p,           // Tx Success
            input  wire            retryLTReached_p,         // Indicates that the retry limit has been reached
            input  wire            txInProgress,             // Tx is ongoing
            
            output reg   [ 3:0]    txDmaState,               // DMA state for the active channel.
            output reg   [15:0]    txOpLimit,                // TXOP Limit of the active channel.
            output wire            backOffDone_p,            // TXOP Limit of the active channel.
            
            //$port_g Timer Interface
            input  wire            noBeaconTxPeriod,         // Period during which the BEACON will not be transmitted
            input  wire            tickDMAEarlySlot_p,       // Early slot pulse, for dma trigger
            input  wire            tickEarlySlot_p,          // Early slot pulse, for Mac controller trigger
            input  wire            tickEarlyTBTT_p,          // Pulse every TBTTs
            input  wire            tickDMAEarlyTBTT_p,       // Pulse prior of tickEarlyTBTT_p
            input  wire            tickSlot_p,              // slot indicator      
            
            //$port_g macPhyIf Interface
            input wire             macPhyIfRxCca,            // CCA

            //$port_g NAV Interface
            input wire             channelBusy,              // Channel Busy

            //$port_g Coex interface
          `ifdef RW_WLAN_COEX_EN
            input  wire            coexWlanTxAbort,          // Requests from external arbiter abort all on-going transmission
          `endif // RW_WLAN_COEX_EN

            //$port_g registers interface                    
            input  wire [15:0]     txOpLimit0,               // Txop registers
            input  wire [15:0]     txOpLimit1,               // Txop registers
            input  wire [15:0]     txOpLimit2,               // Txop registers
            input  wire [15:0]     txOpLimit3,               // Txop registers

            output wire  [15:0]    ac0MOT,                   // medium occupancy timer of AC0
            output wire  [15:0]    ac1MOT,                   // medium occupancy timer of AC1
            output wire  [15:0]    ac3MOT,                   // medium occupancy timer of AC2
            output wire  [15:0]    ac2MOT,                   // medium occupancy timer of AC3
            output reg   [ 7:0]    ac3QSRC,                  // short retry count on AC0
            output reg   [ 7:0]    ac2QSRC,                  // short retry count on AC1
            output reg   [ 7:0]    ac1QSRC,                  // short retry count on AC2
            output reg   [ 7:0]    ac0QSRC,                  // short retry count on AC3
            output reg   [ 7:0]    ac3QLRC,                  // long retry count on AC0
            output reg   [ 7:0]    ac2QLRC,                  // long retry count on AC1
            output reg   [ 7:0]    ac1QLRC,                  // long retry count on AC2
            output reg   [ 7:0]    ac0QLRC,                  // long retry count on AC3
            output reg   [ 2:0]    activeAC,                 // Indicates which AC is currently selected.

            //$port_g dmaRegister interface
            input  wire            ap,                       // indicate the CORE is setup as an AP
            input  wire [ 3: 0]    txAC3State,               // AC0 state
            input  wire [ 3: 0]    txAC2State,               // AC1 state 
            input  wire [ 3: 0]    txAC1State,               // AC2 state 
            input  wire [ 3: 0]    txAC0State,               // AC3 state 
            input  wire [ 3: 0]    txBcnState,               // beacon state 
            input  wire            startTxFrameEx,           // Start Tx frame
            input  wire [ 1: 0]    startTxAC,                // Start Tx AC
            input  wire            bssType,                  // bsstype
            
            output reg             trigTxAC0,                // Backoff done
            output reg             trigTxAC1,                // Backoff done
            output reg             trigTxAC2,                // Backoff done
            output reg             trigTxAC3,                // Backoff done
            output reg             trigTxBcn,                // Backoff done  
            
            //$port_g Backoff counters Interface
            input  wire            backoffDone0,             // backoff counter enable
            input  wire            backoffDone1,             // backoff counter enable
            input  wire            backoffDone2,             // backoff counter enable
            input  wire            backoffDone3,             // backoff counter enable
            
            output wire            retryLtReached0,          // retry limit over
            output wire            retryLtReached1,          // retry limit over
            output wire            retryLtReached2,          // retry limit over
            output wire            retryLtReached3,          // retry limit over
            
            output wire            txFailed0_p,              // Tx Failed
            output wire            txFailed1_p,              // Tx Failed
            output wire            txFailed2_p,              // Tx Failed
            output wire            txFailed3_p,              // Tx Failed
            
            output wire            txSuccessful0_p,          // Tx Success
            output wire            txSuccessful1_p,          // Tx Success
            output wire            txSuccessful2_p,          // Tx Success
            output wire            txSuccessful3_p,          // Tx Success
                        
            output reg             InternalColl0_p,          // backoff Internal collision
            output reg             InternalColl1_p,          // backoff Internal collision
            output reg             InternalColl2_p,          // backoff Internal collision
            output wire            InternalColl3_p,          // backoff Internal collision
           
            output wire            macPhyIfRxCcaGated,       // asserted in IBSS when Beacon queue is programmed            
            output reg             TBTTFlag                  // asserted in IBSS when Beacon queue is programmed



);

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
//PARAMETERS
localparam // HALTED  =  4'd1, // Reset state and SW not yet ready state
              PASSIVE =  4'd2; // Waiting for the trigger from the MAC Controller
           // ACTIVE  =  4'd4, // Currently performing a dma transfer.
           // DEAD    =  4'd8; // Error state. 


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

reg           startIndexCalc_p;       // launch and index calculation

reg  [ 2:0]   backoffDoneIndex;       // backoff Done selected index
reg           backoffDoneIndexValid;  // backoff Done selected index

reg           backoffTrig0;           // indicate the cnt is done, AC triggered
reg           backoffTrig1;
reg           backoffTrig2;
reg           backoffTrig3;

wire [3:0]    trigVector;


reg           trigMacCtrl;              // indicate the MAC controller has to be triggered
reg           backoffDone0_p;           // backoff done
reg           backoffDone1_p;           // backoff done
reg           backoffDone2_p;           // backoff done
reg           backoffDone3_p;           // backoff done

//wire [ 3: 0]  muxedTxAC1State;          // AC1 state after IBSS muxing

reg           tickDMAEarlySlotDelayed_p; 

reg           trigTxBcnDelayed;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Muxing queue 1 input depending on the BSS type

//assign muxedTxAC1State      = (bssType) ? txAC1State : txBcnState;

assign macPhyIfRxCcaGated   = macPhyIfRxCca || (TBTTFlag && ~bssType);

assign InternalColl3_p = 1'b0; // this can never happens

// TBTT flag, indicate the next packet to be sent is a beacon
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    TBTTFlag <= 1'b0;
  else if (!macCoreClkSoftRst_n)
    TBTTFlag <= 1'b0;
  else
  begin
    if ( ((txBcnState == 4'd2) && tickDMAEarlyTBTT_p && ap)                                                             ||
         ((macPhyIfRxCca == 1'b1) && (txInProgress == 1'b0) && (trigTxBcn == 1'b1) && (bssType == 1'b1) && (ap == 1'b1))  )
      TBTTFlag <= 1'b1;
    else if ( (bcnRcved_p && !ap) || (!trigTxBcnDelayed && trigTxBcn) || noBeaconTxPeriod )
      TBTTFlag <= 1'b0;
  end
end

// Delayed version of tickDMAEarlySlot_p
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    tickDMAEarlySlotDelayed_p <= 1'b0;
  else if (!macCoreClkSoftRst_n)
    tickDMAEarlySlotDelayed_p <= 1'b0;
  else
    tickDMAEarlySlotDelayed_p <= tickDMAEarlySlot_p;
end

// Detect a end of count event and trig the required AC
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    backoffTrig0     <= 1'b0; 
    backoffTrig1     <= 1'b0; 
    backoffTrig2     <= 1'b0; 
    backoffTrig3     <= 1'b0; 
    startIndexCalc_p <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n)
  begin
    backoffTrig0     <= 1'b0; 
    backoffTrig1     <= 1'b0; 
    backoffTrig2     <= 1'b0; 
    backoffTrig3     <= 1'b0; 
    startIndexCalc_p <= 1'b0;
  end
  else 
  begin
    // on the DMA early slot, Tx or Rx not active.
    if ((tickDMAEarlySlotDelayed_p  == 1'b1) && !(macPhyIfRxCca || channelBusy || txInProgress))
    begin
      // Trigger the Index calculation
      // 
      if (backoffDone0 == 1'b1 && ((txAC0State == PASSIVE) || (startTxFrameEx && startTxAC == 2'b00)))
      begin
        backoffTrig0     <= 1'b1;
        startIndexCalc_p <= 1'b1;
      end
      if (backoffDone1 == 1'b1 && ((txAC1State == PASSIVE) || (startTxFrameEx && startTxAC == 2'b01) || ((txBcnState == PASSIVE) && (bssType == 1'b0))))
      begin
        backoffTrig1     <= 1'b1;
        startIndexCalc_p <= 1'b1;
      end
      if (backoffDone2 == 1'b1 && ((txAC2State == PASSIVE) || (startTxFrameEx && startTxAC == 2'b10)))
      begin
        backoffTrig2     <= 1'b1;
        startIndexCalc_p <= 1'b1;
      end
      if (backoffDone3 == 1'b1 && ((txAC3State == PASSIVE) || (startTxFrameEx && startTxAC == 2'b11)))
      begin
        backoffTrig3     <= 1'b1;
        startIndexCalc_p <= 1'b1;
      end
    end
    else if (backoffDoneIndexValid == 1'b1)
    begin
      backoffTrig0     <= 1'b0;
      backoffTrig1     <= 1'b0;
      backoffTrig2     <= 1'b0;
      backoffTrig3     <= 1'b0;
      startIndexCalc_p <= 1'b0;
    end
    else
      startIndexCalc_p <= 1'b0;
  end
end

// detect the first trigered queue
assign trigVector[3] = backoffTrig3;
assign trigVector[2] = backoffTrig3   | backoffTrig2;
assign trigVector[1] = trigVector[2]  | backoffTrig1;
assign trigVector[0] = trigVector[1]  | backoffTrig0;

// calculate the index if the triggered queue with the highest priority
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  // Asynchronous reset
  if (!macCoreClkHardRst_n)
  begin
    backoffDoneIndex        <= 3'b00;
    backoffDoneIndexValid   <= 1'b0;  
  end 
  else if (!macCoreClkSoftRst_n)
  begin
    backoffDoneIndex        <= 3'b00;
    backoffDoneIndexValid   <= 1'b0;  
  end 
  else
  begin
    // calculate the index
    if (startIndexCalc_p && (!TBTTFlag || !bssType))    
    begin
      backoffDoneIndex        <=    {2'b0, trigVector[0]} +
                                    {2'b0, trigVector[1]} +
                                    {2'b0, trigVector[2]} +
                                    {2'b0, trigVector[3]} - 3'd1;
                                    
      backoffDoneIndexValid   <= 1'b1;  
    end
    else
    begin
      backoffDoneIndex        <= 3'b00; 
      backoffDoneIndexValid   <= 1'b0;  
    end
  end
end

// save the calculated index
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  // Asynchronous reset
  if (!macCoreClkHardRst_n)
    activeAC <= 3'b0;
  // Synchronous reset
  else if (!macCoreClkSoftRst_n)
    activeAC <= 3'b0;
  else if (trigTxBcn)    
    // save the index
    activeAC <= 3'b100;
  else if (backoffDoneIndexValid)    
    // save the index
    activeAC <= backoffDoneIndex;
end

// generate Done and colision pulses for counter
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    backoffDone0_p    <= 1'b0;
    backoffDone1_p    <= 1'b0;
    backoffDone2_p    <= 1'b0;
    backoffDone3_p    <= 1'b0;
    InternalColl0_p   <= 1'b0;
    InternalColl1_p   <= 1'b0;
    InternalColl2_p   <= 1'b0;
  end 
  else if (!macCoreClkSoftRst_n)
  begin
    backoffDone0_p    <= 1'b0;
    backoffDone1_p    <= 1'b0;
    backoffDone2_p    <= 1'b0;
    backoffDone3_p    <= 1'b0;
    InternalColl0_p   <= 1'b0;
    InternalColl1_p   <= 1'b0;
    InternalColl2_p   <= 1'b0;
  end 
  else
  begin
    // Index has been calculated
    if (backoffDoneIndexValid == 1'b1)    
    begin
      // The queue has been triggered
      if ( backoffTrig0 == 1'b1 )
      begin
        // The priority has been given to this queue
        if ( backoffDoneIndex == 3'b000 ) 
        begin
          backoffDone0_p    <= 1'b1;
          InternalColl0_p   <= 1'b0;
         
        end
        // The priority has NOT been given to this queue
        else
        begin
          backoffDone0_p    <= 1'b0;
          InternalColl0_p   <= 1'b1;
        end
      end
      // The queue has NOT been triggered
      else
      begin
        backoffDone0_p    <= 1'b0;
        InternalColl0_p   <= 1'b0;
      end
      // The queue has been triggered
      if ( backoffTrig1 == 1'b1)
      begin
        // The priority has been given to this queue
        if ( backoffDoneIndex == 3'b001 ) 
        begin
          backoffDone1_p    <= 1'b1;
          InternalColl1_p   <= 1'b0;
         
        end
        // The priority has NOT been given to this queue
        else
        begin
          backoffDone1_p    <= 1'b0;
          InternalColl1_p   <= 1'b1;
        end
      end
      // The queue has NOT been triggered
      else
      begin
        backoffDone1_p    <= 1'b0;
        InternalColl1_p   <= 1'b0;
      end
      // The queue has been triggered
      if ( backoffTrig2 == 1'b1)
      begin
        // The priority has been given to this queue
        if ( backoffDoneIndex == 3'b010 ) 
        begin
          backoffDone2_p    <= 1'b1;
          InternalColl2_p   <= 1'b0;
        end
        // The priority has NOT been given to this queue
        else
        begin
          backoffDone2_p    <= 1'b0;
          InternalColl2_p   <= 1'b1;
        end
      end
      // The queue has NOT been triggered
      else
      begin
        backoffDone2_p    <= 1'b0;
        InternalColl2_p   <= 1'b0;
      end
      // The queue has been triggered
      if ( backoffTrig3 == 1'b1)
      begin
        backoffDone3_p    <= 1'b1;
      end
      // The queue has NOT been triggered
      else
      begin
        backoffDone3_p    <= 1'b0;
      end
    end
    // Reset everything
    else
    begin
      backoffDone0_p    <= 1'b0;
      backoffDone1_p    <= 1'b0;
      backoffDone2_p    <= 1'b0;
      backoffDone3_p    <= 1'b0;
      InternalColl0_p   <= 1'b0;
      InternalColl1_p   <= 1'b0;
      InternalColl2_p   <= 1'b0;
    end
  end
end

// generate Done and colision pulses for counter
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    trigTxAC0    <= 1'b0;
    trigTxAC1    <= 1'b0;
    trigTxAC2    <= 1'b0;
    trigTxAC3    <= 1'b0;
    trigTxBcn    <= 1'b0;
    trigTxBcnDelayed <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n)
  begin
    trigTxAC0    <= 1'b0;
    trigTxAC1    <= 1'b0;
    trigTxAC2    <= 1'b0;
    trigTxAC3    <= 1'b0;
    trigTxBcn    <= 1'b0;
    trigTxBcnDelayed <= 1'b0;
  end
  else
  begin
    trigTxBcnDelayed <= trigTxBcn;
    // When backoff is triggered, triger the DMA
    if (trigTxAC0 || trigTxAC1 || trigTxAC2 || trigTxAC3 || trigTxBcn)
    begin
      // Mac controller restart the backoff
      if ((txSuccessful_p == 1'b1)   ||                         // when packet is successfullly transmitted
          (retry_p == 1'b1)          ||                         // or when it needs to be retried
          (retryLTReached_p == 1'b1) ||                         // or retryLimitReached
          ((macPhyIfRxCca == 1'b1) && (txInProgress == 1'b0)))  // or a reception occurs out of a TxOp
      begin
        trigTxAC0    <= 1'b0;
        trigTxAC1    <= 1'b0;
        trigTxAC2    <= 1'b0;
        trigTxAC3    <= 1'b0;
        trigTxBcn    <= 1'b0;
      end
    end
    else
    begin      
      
      if (backoffDone0_p == 1'b1)
        trigTxAC0    <= 1'b1;
      // When backoff is triggered, triger the DMA
      else if (backoffDone1_p == 1'b1)
      begin
        if (bssType == 1'b1)
          trigTxAC1    <= 1'b1;
        else
          if (noBeaconTxPeriod == 1'b0)
            trigTxBcn    <= 1'b1;
          else
            trigTxBcn    <= 1'b0;
      end
      if ((bssType       == 1'b1) &&
          (TBTTFlag      == 1'b1) && 
          (tickSlot_p    == 1'b1) &&
          (macPhyIfRxCca == 1'b0) &&
          (ap            == 1'b1) &&
    `ifdef RW_WLAN_COEX_EN
          // Postpone the Beacon Transmission if coexWlanTxAbort is set.
          // Trig the Beacon Queue only if coexWlanTxAbort is not set. 
          // Otherwise, the beacon transmission will be postponed
          (!coexWlanTxAbort)      &&
    `endif // RW_WLAN_COEX_EN
          (txInProgress  == 1'b0)   )
        trigTxBcn    <= 1'b1;
      // Mac controller restart the backoff
      // When backoff is triggered, triger the DMA
      if (backoffDone2_p == 1'b1)
        trigTxAC2    <= 1'b1;
      // When backoff is triggered, triger the DMA
      if (backoffDone3_p == 1'b1)
        trigTxAC3    <= 1'b1;
    end    
  end
end


// generate the trigger for the MAC controller
// generate Done and colision pulses for counter
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    trigMacCtrl      <= 1'b0;
  else if (!macCoreClkSoftRst_n)
    trigMacCtrl      <= 1'b0;
  else if (backoffDone0_p || backoffDone1_p || backoffDone2_p || backoffDone3_p)
    trigMacCtrl <= 1'b1;
  else if (macPhyIfRxCca || channelBusy || txInProgress || backOffDone_p)
    trigMacCtrl <= 1'b0;
end

//assign backOffDone_p = ((trigMacCtrl && tickEarlySlot_p) || (trigTxBcn && (tickEarlyTBTT_p || (tickEarlySlot_p && (backoffDone1 || TBTTFlag)))) ) ? 1'b1 : 1'b0;

assign backOffDone_p = ( (trigMacCtrl && tickEarlySlot_p)                                                                        ||   // AC  backoff done
                         ((trigTxBcnDelayed == 1'b0) && (trigTxBcn == 1'b1) && (macPhyIfRxCca == 1'b0) && (txInProgress == 1'b0))  ); // Bcn backoff done (when rising edge of trigTxBcn is detected)

// redirect retry limit reached
assign retryLtReached0 = ((activeAC == 3'b000) && (retryLTReached_p == 1'b1)) ? 1'b1 : 1'b0;
assign retryLtReached1 = ((activeAC == 3'b001) && (retryLTReached_p == 1'b1)) ? 1'b1 : 1'b0;
assign retryLtReached2 = ((activeAC == 3'b010) && (retryLTReached_p == 1'b1)) ? 1'b1 : 1'b0;
assign retryLtReached3 = ((activeAC == 3'b011) && (retryLTReached_p == 1'b1)) ? 1'b1 : 1'b0;

// rediect retry failed
assign txFailed0_p     = ((activeAC == 3'b000) && (retry_p == 1'b1)) ? 1'b1 : 1'b0;
assign txFailed1_p     = ((activeAC == 3'b001) && (retry_p == 1'b1)) ? 1'b1 : 1'b0;
assign txFailed2_p     = ((activeAC == 3'b010) && (retry_p == 1'b1)) ? 1'b1 : 1'b0;
assign txFailed3_p     = ((activeAC == 3'b011) && (retry_p == 1'b1)) ? 1'b1 : 1'b0;

// redirect Tx successful
assign txSuccessful0_p = ((activeAC == 3'b000) && (txSuccessful_p == 1'b1)) ? 1'b1 : 1'b0;
assign txSuccessful1_p = ((activeAC == 3'b001) && (txSuccessful_p == 1'b1)) ? 1'b1 : 1'b0;
assign txSuccessful2_p = ((activeAC == 3'b010) && (txSuccessful_p == 1'b1)) ? 1'b1 : 1'b0;
assign txSuccessful3_p = ((activeAC == 3'b011) && (txSuccessful_p == 1'b1)) ? 1'b1 : 1'b0;

// redirect MOT
assign ac0MOT          = (activeAC == 3'b000) ? acMOT : txOpLimit0;
assign ac1MOT          = (activeAC == 3'b001) ? acMOT : txOpLimit1;
assign ac2MOT          = (activeAC == 3'b010) ? acMOT : txOpLimit2;
assign ac3MOT          = (activeAC == 3'b011) ? acMOT : txOpLimit3;


// Mux data to MAC Controller
always @*
begin
  case(activeAC)
    3'b000:
    begin
      txDmaState = txAC0State;
      txOpLimit  = txOpLimit0;
    end

    3'b001:
    begin
      txDmaState = txAC1State;
      txOpLimit  = txOpLimit1;
    end

    3'b010:
    begin
      txDmaState = txAC2State;
      txOpLimit  = txOpLimit2;
    end

    3'b011:
    begin
      txDmaState = txAC3State;
      txOpLimit  = txOpLimit3;
    end

    3'b100:
    begin
      txDmaState = txBcnState;
      txOpLimit  = 16'h0;
    end

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:   
    begin
      txDmaState = txAC0State;
      txOpLimit  = txOpLimit0;
    end
    // pragma coverage block = on 

  endcase
end

// retry count registers
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    ac3QSRC    <= 8'b0;
    ac2QSRC    <= 8'b0;
    ac1QSRC    <= 8'b0;
    ac0QSRC    <= 8'b0;
    ac3QLRC    <= 8'b0;
    ac2QLRC    <= 8'b0;
    ac1QLRC    <= 8'b0;
    ac0QLRC    <= 8'b0;
  end
  else if (!macCoreClkSoftRst_n)
  begin
    ac3QSRC    <= 8'b0;
    ac2QSRC    <= 8'b0;
    ac1QSRC    <= 8'b0;
    ac0QSRC    <= 8'b0;
    ac3QLRC    <= 8'b0;
    ac2QLRC    <= 8'b0;
    ac1QLRC    <= 8'b0;
    ac0QLRC    <= 8'b0;
  end
  else
  begin
    if (txSuccessful_p || retryLTReached_p)
    begin
      case(activeAC)
        3'b000:
        begin
          ac0QLRC    <= 8'b0;
          ac0QSRC    <= 8'b0;
        end
        3'b001:
        begin
          ac1QLRC    <= 8'b0;
          ac1QSRC    <= 8'b0;
        end
        3'b010:
        begin
          ac2QLRC    <= 8'b0;
          ac2QSRC    <= 8'b0;
        end
        3'b011:
        begin
          ac3QLRC    <= 8'b0;
          ac3QSRC    <= 8'b0;
        end

        default:
        begin   
          ac3QSRC    <= 8'b0;
          ac2QSRC    <= 8'b0;
          ac1QSRC    <= 8'b0;
          ac0QSRC    <= 8'b0;
          ac3QLRC    <= 8'b0;
          ac2QLRC    <= 8'b0;
          ac1QLRC    <= 8'b0;
          ac0QLRC    <= 8'b0;
        end

      endcase
    end
    else if (retry_p)
      case(activeAC)
        3'b000:
        begin
          if (retryType == 1'b1)
            ac0QLRC    <= ac0QLRC + 8'd1;
          else
            ac0QSRC    <= ac0QSRC + 8'd1;
        end
        3'b001:
        begin
          if (retryType == 1'b1)
            ac1QLRC    <= ac1QLRC + 8'd1;
          else
            ac1QSRC    <= ac1QSRC + 8'd1;
        end
        3'b010:
        begin
          if (retryType == 1'b1)
            ac2QLRC    <= ac2QLRC + 8'd1;
          else
            ac2QSRC    <= ac2QSRC + 8'd1;
        end
        3'b011:
        begin
          if (retryType == 1'b1)
            ac3QLRC    <= ac3QLRC + 8'd1;
          else
            ac3QSRC    <= ac3QSRC + 8'd1;
        end
        default:   
        begin   
          ac3QSRC    <= 8'b0;
          ac2QSRC    <= 8'b0;
          ac1QSRC    <= 8'b0;
          ac0QSRC    <= 8'b0;
          ac3QLRC    <= 8'b0;
          ac2QLRC    <= 8'b0;
          ac1QLRC    <= 8'b0;
          ac0QLRC    <= 8'b0;
        end
      endcase
  end
end



///////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////
// System Verilog Assertions
///////////////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva This cover point checks if we have generate a backoff for the queue 0
checkDone0: cover property (@(posedge macCoreClk) (backoffDone0_p));
//$rw_sva This cover point checks if we have generate a backoff for the queue 1
checkDone1: cover property (@(posedge macCoreClk) (backoffDone1_p));
//$rw_sva This cover point checks if we have generate a backoff for the queue 2
checkDone2: cover property (@(posedge macCoreClk) (backoffDone2_p));
//$rw_sva This cover point checks if we have generate a backoff for the queue 3
checkDone3: cover property (@(posedge macCoreClk) (backoffDone3_p));

//$rw_sva This cover point checks if we have generate a collsion for the queue 0
checkCollision0: cover property (@(posedge macCoreClk) (InternalColl0_p));
//$rw_sva This cover point checks if we have generate a collsion for the queue 1
checkCollision1: cover property (@(posedge macCoreClk) (InternalColl1_p));
//$rw_sva This cover point checks if we have generate a collsion for the queue 2
checkCollision2: cover property (@(posedge macCoreClk) (InternalColl2_p));

//$rw_sva Check for BackoffDone is a single clock cycle pulse
property backoffDone0_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  backoffDone0_p |=>!backoffDone0_p;
endproperty
backoffDone0_pulse: assert property (backoffDone0_pulse_prop); 

//$rw_sva Check for BackoffDone is a single clock cycle pulse
property backoffDone1_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  backoffDone1_p |=>!backoffDone1_p;
endproperty
backoffDone1_pulse: assert property (backoffDone1_pulse_prop); 

//$rw_sva Check for BackoffDone is a single clock cycle pulse
property backoffDone2_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  backoffDone2_p |=>!backoffDone2_p;
endproperty
backoffDone2_pulse: assert property (backoffDone2_pulse_prop); 

//$rw_sva Check for BackoffDone is a single clock cycle pulse
property backoffDone3_pulse_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  backoffDone3_p |=>!backoffDone3_p;
endproperty
backoffDone3_pulse: assert property (backoffDone3_pulse_prop); 

//$rw_sva Check there is no collision when TBTTflag is asserted
property no_collission_when_tbtt_flag_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  TBTTFlag |-> !(InternalColl0_p || InternalColl1_p ||InternalColl2_p);
endproperty
no_collission_when_tbtt_flag: assert property (no_collission_when_tbtt_flag_prop); 



`endif // RW_ASSERT_ON

endmodule
                 
