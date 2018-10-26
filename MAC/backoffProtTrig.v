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

module backoffProtTrig( 
            //$port_g Clock and Reset
            input  wire            macCoreClk,              // MAC core clock      
            input  wire            macCoreClkHardRst_n,     // MAC core clock reset
            
            input  wire            macCoreClkSoftRst_n,     // MAC core clock soft reset
            
            //$port_g backoff core state
            input  wire            backoffEnable,           // core status
            input  wire            currentStateEvent,       // core state event
            
            //$port_g mac Controller interface
            input  wire            txInProgress,            // Tx is ongoing
            
            //$port_g DMA interface 
            input  wire [ 3:0]     txAC3State,              // AC0 state
            input  wire [ 3:0]     txAC2State,              // AC1 state 
            input  wire [ 3:0]     txAC1State,              // AC2 state 
            input  wire [ 3:0]     txAC0State,              // AC3 state 
            
            //$port_g backoff counter interface 
            input  wire [15:0]     backoffCnt0,             // backoff counter
            input  wire [15:0]     backoffCnt1,             // backoff counter
            input  wire [15:0]     backoffCnt2,             // backoff counter
            input  wire [15:0]     backoffCnt3,             // backoff counter

            //$port_g timer unit interface
            input  wire [11:0]     aifsCnt0,                // AIFS0 counter
            input  wire [11:0]     aifsCnt1,                // AIFS1 counter
            input  wire [11:0]     aifsCnt2,                // AIFS2 counter
            input  wire [11:0]     aifsCnt3,                // AIFS3 counter
            input  wire [ 7:0]     slotCnt,                 // Slot counter
            input  wire            tickSlot1us_p,           // microsecond tick aligned on slotcnt
             
            //port_g registers interface
            input  wire [ 7:0]     edcaTriggerTimer,        // $todo implement HCCA trigger Timer 
            input  wire [ 7:0]     slotTime,                // slot time
            input  wire            setac3HasData,           // set ac3 has data
            input  wire            setac2HasData,           // set ac2 has data
            input  wire            setac1HasData,           // set ac1 has data
            input  wire            setac0HasData,           // set ac0 has data
            input  wire            clearac3HasData,         // clear ac3 has data
            input  wire            clearac2HasData,         // clear ac2 has data
            input  wire            clearac1HasData,         // clear ac1 has data
            input  wire            clearac0HasData,         // clear ac0 has data
            
            output reg             statussetac3HasData,     // ac3 has data status
            output reg             statussetac2HasData,     // ac2 has data status
            output reg             statussetac1HasData,     // ac1 has data status
            output reg             statussetac0HasData,     // ac0 has data status
            output wire [ 7:0]     hccaTriggerTimer,        // EDCA trigger Timer 
            
            //$port_g interrupt controller interface
            input  wire            ac3ProtTriggerFlagReset, // ac3 protocol trigger reset
            input  wire            ac2ProtTriggerFlagReset, // ac2 protocol trigger reset
            input  wire            ac1ProtTriggerFlagReset, // ac1 protocol trigger reset
            input  wire            ac0ProtTriggerFlagReset, // ac0 protocol trigger reset
            //
            output reg             ac3ProtTrigger,          // ac3 protocol trigger event
            output reg             ac2ProtTrigger,          // ac2 protocol trigger event
            output reg             ac1ProtTrigger,          // ac1 protocol trigger event
            output reg             ac0ProtTrigger           // ac0 protocol trigger event

);


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////
localparam // HALTED  =  4'd1, // Reset state and SW not yet ready state
           PASSIVE =  4'd2, // Waiting for the trigger from the MAC Controller
           ACTIVE  =  4'd4; // Currently performing a dma transfer.
           // DEAD    =  4'd8; // Error state. 



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
reg           ac3Trig;                       // ac3 protocol trigger internal event
reg           ac2Trig;                       // ac2 protocol trigger internal event
reg           ac1Trig;                       // ac1 protocol trigger internal event
reg           ac0Trig;                       // ac0 protocol trigger internal event

reg           ac3ProtTriggerFlag;            // ac3 protocol trigger event flag
reg           ac2ProtTriggerFlag;            // ac2 protocol trigger event flag
reg           ac1ProtTriggerFlag;            // ac1 protocol trigger event flag
reg           ac0ProtTriggerFlag;            // ac0 protocol trigger event flag

reg  [ 3:0]  trigVector;                     // trigerred vector for AC selection
wire         checkCollision;                 // a triggered occured, check if there is collision
reg  [ 2:0]  earlyTriggerIndex     ;         // most important active index
reg          earlyTriggerIndexValid;         // a by priority filtered index is available
// wire [ 2:0]  CollisionCnt;                   // number of triggered vectors

reg          tickSlot1usDelayed_p;           // save slotCnt1

reg  [15:0]  triggerslotValue;               // indicate which backcount will trigger
reg  [15:0]  triggerCntValue;                // indicate which slotcount will trigger
reg          triggerCalcDone;                // calculation of the backcount which  will trigger is done
reg          triggerCalcEn;                  // calculation of the backcount which  will trigger is enabled
reg  [ 2:0]  shiftIndex;                     // how much do we shift the slotTime value

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

assign hccaTriggerTimer = 8'b0;


// generate 1 clock cycle delayed tickSlot1us_p
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
    tickSlot1usDelayed_p <= 1'b0;
  else if (!macCoreClkSoftRst_n)
    tickSlot1usDelayed_p <= 1'b0;
  else
    tickSlot1usDelayed_p <= tickSlot1us_p;
end



// calculate triggerslotValue 
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    triggerslotValue           <= 16'b0;
    triggerCntValue            <= 16'b0;
    triggerCalcDone            <=  1'b0;
    triggerCalcEn              <=  1'b0;
    shiftIndex                 <=  3'd7;
  end
  else if (!macCoreClkSoftRst_n)
  begin
    triggerslotValue           <= 16'b0;
    triggerCntValue            <= 16'b0;
    triggerCalcDone            <=  1'b0;
    triggerCalcEn              <=  1'b0;
    shiftIndex                 <=  3'd7;
  end
  else
  begin
    //enable the triggerslotValue calculation
    // and reset all the variables value
    if (currentStateEvent == 1'b1)
    begin
      triggerCalcEn             <=  1'b1;
      triggerCalcDone           <=  1'b0;
      triggerslotValue          <= 16'b0;
      triggerCntValue           <= {8'h00,edcaTriggerTimer};
      shiftIndex                <=  3'd7;
    end
    //disable the triggerslotValue calculation
    else if (triggerCalcDone == 1'b1)
      triggerCalcEn <= 1'b0;
    
    if (triggerCalcEn == 1'b1)
    begin
      if (triggerCntValue >= ({8'd0,slotTime}<<shiftIndex) )
      begin
        triggerCntValue              <= triggerCntValue - ({8'd0,slotTime}<<shiftIndex);
        triggerslotValue[shiftIndex] <= 1'b1;
      end
      shiftIndex <= shiftIndex - 3'd1;
      
      if (shiftIndex == 3'b0)
        triggerCalcDone           <= 1'b1;
    end    
  end
end

// Control has data registers
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    statussetac3HasData    <= 1'b0;
    statussetac2HasData    <= 1'b0;
    statussetac1HasData    <= 1'b0;
    statussetac0HasData    <= 1'b0;
  end
  else if (!macCoreClkSoftRst_n)
  begin
    statussetac3HasData    <= 1'b0;
    statussetac2HasData    <= 1'b0;
    statussetac1HasData    <= 1'b0;
    statussetac0HasData    <= 1'b0;
  end
  else
  begin
    if ( setac3HasData == 1'b1)
      statussetac3HasData    <= 1'b1;
    else if (clearac3HasData)  
      statussetac3HasData    <= 1'b0;
    if ( setac2HasData == 1'b1)
      statussetac2HasData    <= 1'b1;
    else if (clearac2HasData)  
      statussetac2HasData    <= 1'b0;
    if ( setac1HasData == 1'b1)
      statussetac1HasData    <= 1'b1;
    else if (clearac1HasData)  
      statussetac1HasData    <= 1'b0;
    if ( setac0HasData == 1'b1)
      statussetac0HasData    <= 1'b1;
    else if (clearac0HasData)  
      statussetac0HasData    <= 1'b0;
  end
end  

// detect the triggered queue. Will be filtered by AC Selection
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  if (!macCoreClkHardRst_n)
  begin
    ac3Trig <= 1'b0;                   
    ac2Trig <= 1'b0;                   
    ac1Trig <= 1'b0;                   
    ac0Trig <= 1'b0;                   
  end
  else if (!macCoreClkSoftRst_n)
  begin
    ac3Trig <= 1'b0;                   
    ac2Trig <= 1'b0;                   
    ac1Trig <= 1'b0;                   
    ac0Trig <= 1'b0;                   
  end
  else
  begin
    if (backoffEnable == 1'b1)
    begin  
      if (tickSlot1us_p == 1'b1)                      
      begin                                  
        // backoff count less than the slot trigger value
        if (backoffCnt3 == triggerslotValue) 
        begin                                
          // check aifs count                
          if ( aifsCnt3 == 12'd0 )               
          begin                              
            // check slot count              
            if (slotCnt <= triggerCntValue[7:0])  
              ac3Trig           <= 1'b1;      
            else                             
              ac3Trig           <= 1'b0;      
          end                                
          else                               
          begin                              
            // check aifs count              
            if (aifsCnt3 <= triggerCntValue[11:0]) 
              ac3Trig           <= 1'b1;      
            else                             
              ac3Trig           <= 1'b0;      
          end                                
        end
        else if (backoffCnt3 < triggerslotValue) 
          ac3Trig           <= 1'b1;      
        else
          ac3Trig           <= 1'b0;      
        // backoff count less than the slot trigger value
        if (backoffCnt2 == triggerslotValue) 
        begin                                
          // check aifs count                
          if ( aifsCnt2 == 12'd0 )               
          begin                              
            // check slot count              
            if (slotCnt <= triggerCntValue[7:0])  
              ac2Trig           <= 1'b1;      
            else                             
              ac2Trig           <= 1'b0;      
          end                                
          else                               
          begin                              
            // check aifs count              
            if (aifsCnt2 <= triggerCntValue[11:0]) 
              ac2Trig           <= 1'b1;      
            else                             
              ac2Trig           <= 1'b0;      
          end                                
        end
        else if (backoffCnt2 < triggerslotValue) 
          ac2Trig           <= 1'b1;      
        else
          ac2Trig           <= 1'b0;      
        // backoff count less than the slot trigger value
        if (backoffCnt1 == triggerslotValue) 
        begin                                
          // check aifs count                
          if ( aifsCnt1 == 12'd0 )               
          begin                              
            // check slot count              
            if (slotCnt <= triggerCntValue[7:0])  
              ac1Trig           <= 1'b1;      
            else                             
              ac1Trig           <= 1'b0;      
          end                                
          else                               
          begin                              
            // check aifs count              
            if (aifsCnt1 <= triggerCntValue[11:0]) 
              ac1Trig           <= 1'b1;      
            else                             
              ac1Trig           <= 1'b0;      
          end                                
        end                                  
        else if (backoffCnt1 < triggerslotValue) 
          ac1Trig           <= 1'b1;      
        else
          ac1Trig           <= 1'b0;      
        // backoff count less than the slot trigger value
        if (backoffCnt0 == triggerslotValue) 
        begin                                
          // check aifs count                
          if ( aifsCnt0 == 12'd0 )               
          begin                              
            // check slot count              
            if (slotCnt <= triggerCntValue[7:0])  
              ac0Trig           <= 1'b1;      
            else                             
              ac0Trig           <= 1'b0;      
          end                                
          else                               
          begin                              
            // check aifs count              
            if (aifsCnt0 <= triggerCntValue[11:0]) 
              ac0Trig           <= 1'b1;      
            else                             
              ac0Trig           <= 1'b0;      
          end                                
        end                                  
        else if (backoffCnt0 < triggerslotValue) 
          ac0Trig           <= 1'b1;      
        else
          ac0Trig           <= 1'b0;      
      end                                    
      else                                   
      begin                                  
        ac3Trig <= ac3Trig;                   
        ac2Trig <= ac2Trig;                   
        ac1Trig <= ac1Trig;                   
        ac0Trig <= ac0Trig;                   
      end
    end
    else
    begin
      ac3Trig <= 1'b0;                 
      ac2Trig <= 1'b0;                 
      ac1Trig <= 1'b0;                 
      ac0Trig <= 1'b0;                 
    end                                    
  end
end


// start the processing to look for Protocol trigger collision
assign checkCollision  = (ac0Trig | ac1Trig | ac2Trig | ac3Trig) && tickSlot1usDelayed_p; 


// Count the number of trigger vector
// assign CollisionCnt    = {2'b00, ac0Trig} + 
//                          {2'b00, ac1Trig} + 
//                          {2'b00, ac2Trig} + 
//                          {2'b00, ac3Trig} ;
                         

always @*
begin
  if (checkCollision == 1'b1) 
  begin
    trigVector[3] =                  (ac3Trig && (statussetac3HasData || txAC3State == PASSIVE || txAC3State == ACTIVE));
    trigVector[2] = trigVector[3] || (ac2Trig && (statussetac2HasData || txAC2State == PASSIVE || txAC2State == ACTIVE));
    trigVector[1] = trigVector[2] || (ac1Trig && (statussetac1HasData || txAC1State == PASSIVE || txAC1State == ACTIVE));
    trigVector[0] = trigVector[1] || (ac0Trig && (statussetac0HasData || txAC0State == PASSIVE || txAC0State == ACTIVE));
  end
  else
  begin
    trigVector = 4'b0;
  end
end

// calculate the index if the triggered queue with the highest priority
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  // Asynchronous reset
  if (!macCoreClkHardRst_n)
  begin
    earlyTriggerIndex        <= 3'b0;
    earlyTriggerIndexValid   <= 1'b0;  
  end 
  // Synchronous reset
  else if (!macCoreClkSoftRst_n)
  begin
    earlyTriggerIndex        <= 3'b0;
    earlyTriggerIndexValid   <= 1'b0;  
  end 
  else
  begin
    // calculate the index
    if ((checkCollision == 1'b1) && (trigVector != 4'b0))    
    begin
      earlyTriggerIndexValid   <= 1'b1;  
      earlyTriggerIndex        <= {2'b00, trigVector[0]} +
                                  {2'b00, trigVector[1]} +
                                  {2'b00, trigVector[2]} +
                                  {2'b00, trigVector[3]} - 3'd1;
    end
    else
    begin
      earlyTriggerIndex        <= 3'b0; 
      earlyTriggerIndexValid   <= 1'b0;  
    end
  end
end

// generate the protocol trigger pulse for the interrupt controller
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  // Asynchronous reset
  if (!macCoreClkHardRst_n)
  begin
    ac3ProtTrigger         <= 1'b0;
    ac2ProtTrigger         <= 1'b0;
    ac1ProtTrigger         <= 1'b0;
    ac0ProtTrigger         <= 1'b0;
  end 
  // Synchronous reset
  else if (!macCoreClkSoftRst_n)
  begin
    ac3ProtTrigger         <= 1'b0;
    ac2ProtTrigger         <= 1'b0;
    ac1ProtTrigger         <= 1'b0;
    ac0ProtTrigger         <= 1'b0;
  end 
  else
  begin
    // if an index is valid, generate pulse
    if (earlyTriggerIndexValid &&  txInProgress == 1'b0)    
    begin
      
      ac3ProtTrigger <= 1'b0;
      ac2ProtTrigger <= 1'b0;
      ac1ProtTrigger <= 1'b0;
      ac0ProtTrigger <= 1'b0;  

      case(earlyTriggerIndex[1:0])
        2'd0:
          if (ac0ProtTriggerFlag == 1'b0 && statussetac0HasData == 1'b1)
            ac0ProtTrigger <= 1'b1;  
        2'd1:
          if (ac1ProtTriggerFlag == 1'b0 && statussetac1HasData == 1'b1)
            ac1ProtTrigger <= 1'b1;
        2'd2:
          if (ac2ProtTriggerFlag == 1'b0 && statussetac2HasData == 1'b1)
            ac2ProtTrigger <= 1'b1;
        2'd3:
          if (ac3ProtTriggerFlag == 1'b0 && statussetac3HasData == 1'b1)
            ac3ProtTrigger <= 1'b1;
        // Disable coverage on the default state because it cannot be reached.
        // pragma coverage block = off
        default:
        begin
          ac3ProtTrigger         <= 1'b0;
          ac2ProtTrigger         <= 1'b0;
          ac1ProtTrigger         <= 1'b0;
          ac0ProtTrigger         <= 1'b0;
        end
        // pragma coverage block = on
      endcase
    end
    else
    begin
      ac3ProtTrigger         <= 1'b0;
      ac2ProtTrigger         <= 1'b0;
      ac1ProtTrigger         <= 1'b0;
      ac0ProtTrigger         <= 1'b0;
    end
  end
end

// generate the protocol trigger flag to memorize the interruption
// then it will be asserted only once until the queue transmit 
always @(posedge macCoreClk or negedge macCoreClkHardRst_n)
begin
  // Asynchronous reset
  if (!macCoreClkHardRst_n)
  begin
    ac3ProtTriggerFlag     <= 1'b0;
    ac2ProtTriggerFlag     <= 1'b0;
    ac1ProtTriggerFlag     <= 1'b0;
    ac0ProtTriggerFlag     <= 1'b0;
  end 
  // Synchronous reset
  else if (!macCoreClkSoftRst_n)
  begin
    ac3ProtTriggerFlag     <= 1'b0;
    ac2ProtTriggerFlag     <= 1'b0;
    ac1ProtTriggerFlag     <= 1'b0;
    ac0ProtTriggerFlag     <= 1'b0;
  end 
  else
  begin
    // check there is a protocol trigger 
    if ( ac3ProtTrigger == 1'b1 && txInProgress == 1'b0)
      ac3ProtTriggerFlag     <= 1'b1;
    // reset the Flag when the queue become active
    else if ( ac3ProtTriggerFlagReset == 1'b1 || clearac3HasData == 1'b1) 
      ac3ProtTriggerFlag     <= 1'b0;
    // check there is a protocol trigger 
    if ( ac2ProtTrigger == 1'b1)
      ac2ProtTriggerFlag     <= 1'b1;
    // reset the Flag when the queue become active
    else if ( ac2ProtTriggerFlagReset == 1'b1 || clearac2HasData == 1'b1) 
      ac2ProtTriggerFlag     <= 1'b0;
    // check there is a protocol trigger 
    if ( ac1ProtTrigger == 1'b1)
      ac1ProtTriggerFlag     <= 1'b1;
    // reset the Flag when the queue become active
    else if ( ac1ProtTriggerFlagReset == 1'b1 || clearac1HasData == 1'b1) 
      ac1ProtTriggerFlag     <= 1'b0;
    // check there is a protocol trigger 
    if ( ac0ProtTrigger == 1'b1)
      ac0ProtTriggerFlag     <= 1'b1;
    // reset the Flag when the queue become active
    else if ( ac0ProtTriggerFlagReset == 1'b1 || clearac0HasData == 1'b1) 
      ac0ProtTriggerFlag     <= 1'b0;
  end
end



`ifdef RW_ASSERT_ON
//$rw_sva Check for protocol triggers are mutuallly exclusive
property ProtTrigger_exclusive0_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac0ProtTrigger |->!(ac1ProtTrigger | ac2ProtTrigger | ac3ProtTrigger);
endproperty
ProtTrigger_exclusive0: assert property (ProtTrigger_exclusive0_prop); 

//$rw_sva Check for protocol triggers are mutuallly exclusive
property ProtTrigger_exclusive1_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac1ProtTrigger |->!(ac0ProtTrigger | ac2ProtTrigger | ac3ProtTrigger);
endproperty
ProtTrigger_exclusive1: assert property (ProtTrigger_exclusive1_prop); 

//$rw_sva Check for protocol triggers are mutuallly exclusive
property ProtTrigger_exclusive2_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac2ProtTrigger |->!(ac0ProtTrigger | ac1ProtTrigger | ac3ProtTrigger);
endproperty
ProtTrigger_exclusive2: assert property (ProtTrigger_exclusive2_prop); 

//$rw_sva Check for protocol triggers are mutuallly exclusive
property ProtTrigger_exclusive3_prop;
@(posedge macCoreClk)
  disable iff(macCoreClkHardRst_n==0)
  ac3ProtTrigger |->!(ac0ProtTrigger | ac1ProtTrigger | ac2ProtTrigger);
endproperty
ProtTrigger_exclusive3: assert property (ProtTrigger_exclusive3_prop); 

`endif // RW_ASSERT_ON



endmodule
                 
