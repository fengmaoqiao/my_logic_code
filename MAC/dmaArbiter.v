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
// Description      : This module arbites the access to the Read Write
//                    Controller from receive list processor,Status Updater
//                    and transmit list processor in the same priority.
// Simulation Notes : 
// Synthesis Notes  : 
// Application Note :                                                       
// Simulator        :                                                       
// Parameters       :                                                       
// Terms & concepts :                                                       
// Bugs             :
// References       :                                                       
// Revision History :                                                       
// ---------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


module dmaArbiter(
         //Port Definitions
         
         //$port_g Clock and Reset interface
         input  wire       macPIClk,               //Platform clk domain
         input  wire       macPIClkHardRst_n,      //Hard Reset synchronized to macPIClk,
         input  wire       macPIClkSoftRst_n,      //Soft Reset synchronized to macPIClk,
          
         //$port_g rdWrCtrl interface
         input  wire       rdWrCtlrIdle,           // the controller is idle
         
         
         //$port_g rxListProc interface
         input  wire       rxListProcReq,          //Receive List Processor request for grant from arbiter
         //          
         output wire       rxListProcGrant,        //Grant for the recieve list processor
        
         //$port_g status updater interface
         input  wire       txStaUpdaterReq,        //Status Updater request for grant from arbiter
         // 
         output wire       txStaUpdaterGrant,      //Grant for Transmit Updater
         
         //$port_g txListProc interface
         input  wire       txListProcReq,          //Transmit List Processor request for grant from arbiter
         //
         output wire       txListProcGrant         //Grant for Transmit List Processor
);

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

// dmaArbiter FSM states definition
//$fsm_sd dmaArbiter
localparam IDLE         = 2'h0, //FSM stays here until req for grant is asserted
           RX_GRANT     = 2'h1, //Receive List processor is given grant
           STATUS_GRANT = 2'h2, //Status Updater is given grant
           TX_GRANT     = 2'h3; //Transmit List processor is given grant


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

reg  [1:0] dmaArbiterCs;      //Current State for Arbiter FSM
reg  [1:0] dmaArbiterNs;      //Next State for Arbiter FSM

`ifdef RW_SIMU_ON
// String definition to display dmaArbiter current state
reg [20*8:0] dmaArbiterCs_str;
`endif // RW_SIMU_ON

//Logic for Current State
always @(posedge macPIClk or negedge macPIClkHardRst_n)
begin
  if (macPIClkHardRst_n == 1'b0)
    dmaArbiterCs <= IDLE;
  else if (macPIClkSoftRst_n == 1'b0)
    dmaArbiterCs <= IDLE;
  else 
    dmaArbiterCs <= dmaArbiterNs;
end

//Logic for Next State
//The priority is given to recieve list processor then
//status updater and then transmit list processor.
//In the RX_GRANT and the TX_GRANT states if the rxFifoEmpty
//and the txFifoAlmostFull condition occurs the FSM moves to IDLE
//and the next active request according to priority is serviced
always @*
begin
  case (dmaArbiterCs)

    IDLE: 
      //$fsm_s The FSM starts in this state after reset. 
      //FSM waits in this state until a request is received from any of the 
      //three blocks Receive List Processor, Transmit Status Updater and Transmit List Processor. 
      //Grant is given on priority basis.
      if (rdWrCtlrIdle == 1'b1)
      begin
        if (rxListProcReq == 1'b1)
          //$fsm_t When rxListProcReq is received and the rdWrCtlrIdle is set, the FSM moves to RX_GRANT to grant the
          // access to the Receive List Processor
          dmaArbiterNs = RX_GRANT;
        else if (txStaUpdaterReq == 1'b1)
          //$fsm_t When txStaUpdaterReq is received and the rdWrCtlrIdle is set, the FSM moves to STATUS_GRANT to grant the
          // access to the Transmit Status Updater
          dmaArbiterNs = STATUS_GRANT;
        else if (txListProcReq   == 1'b1 )
          //$fsm_t When txListProcReq is received and the rdWrCtlrIdle is set, the FSM moves to TX_GRANT to grant the
          // access to the Transmit List Processor
          dmaArbiterNs = TX_GRANT;
        else 
          //$fsm_t If rdWrCtlrIdle is set but not request have been received, the FSM stays in IDLE
          dmaArbiterNs = IDLE;
      end
      else
        //$fsm_t If rdWrCtlrIdle is not set, the FSM stays in IDLE
        dmaArbiterNs = IDLE;

    RX_GRANT:
      //$fsm_s The FSM stays here until there is no
      //active request from the receive list processor
      //or if the fifo is empty
      if (rxListProcReq == 1'b0 )
        //$fsm_t When the receive list processor processing is completed (indicated by rxListProcReq low), 
        //the FSM moves back to IDLE
        dmaArbiterNs = IDLE;
      else
        //$fsm_t While rxListProcReq is set, the FSM stays in RX_GRANT
        dmaArbiterNs = RX_GRANT;

    STATUS_GRANT:
      //$fsm_s The FSM stays here until there is no active request from 
      //status updater 
      if (txStaUpdaterReq == 1'b0)
        //$fsm_t When the status update is completed (indicated by txStaUpdaterReq low), 
        //the FSM moves back to IDLE
        dmaArbiterNs = IDLE;
      else
        //$fsm_t While txStaUpdaterReq is set, the FSM stays in STATUS_GRANT
        dmaArbiterNs = STATUS_GRANT;

    TX_GRANT:
      //$fsm_s The FSM stays here until the burst is completed
      //and there is no active request from the 
      //transmit list processor 
      if (txListProcReq == 1'b0)
        //$fsm_t When the transmit list processor processing is completed (indicated by txListProcReq low), 
        //the FSM moves back to IDLE
        dmaArbiterNs = IDLE;
      else
        //$fsm_t While txListProcReq is set, the FSM stays in TX_GRANT
        dmaArbiterNs = TX_GRANT;

    // Disable coverage on the default state because it cannot be reached.
    // pragma coverage block = off 
    default:
      dmaArbiterNs = IDLE;      
    // pragma coverage block = on 

  endcase
end

//The grant signals are asserted when the FSM reaches their respective states. 
assign txListProcGrant      = (dmaArbiterCs == TX_GRANT) ? 1'b1 : 1'b0;

assign rxListProcGrant      = (dmaArbiterCs == RX_GRANT) ? 1'b1 : 1'b0;

assign txStaUpdaterGrant    = (dmaArbiterCs == STATUS_GRANT) ? 1'b1 : 1'b0;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 
// dmaArbiterCs FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (dmaArbiterCs)
        IDLE           :  dmaArbiterCs_str = {"IDLE"};        
        RX_GRANT       :  dmaArbiterCs_str = {"RX_GRANT"};        
        STATUS_GRANT   :  dmaArbiterCs_str = {"STATUS_GRANT"};        
        TX_GRANT       :  dmaArbiterCs_str = {"TX_GRANT"};        
        default        :  dmaArbiterCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

endmodule
