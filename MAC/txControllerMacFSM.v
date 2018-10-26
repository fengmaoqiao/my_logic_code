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
//                    
//    For simulation, one define is available
//
//    RW_SIMU_ON   : which creates string signals to display the FSM states on  
//                the waveform viewers
//
// Some pragmas for code coverage have been defined.
//  - The implicite default state has been excluded
//  - The some default states have been excluded because not reachable by design
// pragma coverage implicit_default=off 
//
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


module txControllerMainFSM( 
          //$port_g Clock and Reset interface
          input  wire        macCoreTxClk,          // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n, // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreTxClkSoftRst_n, // Soft Reset of the MAC Core Clock domain 
                                                    // active low
          //$port_g MAC Controller interface
          input  wire        sendData_p,            // indicates that data packet has to be sent
          input  wire        sendRTS_p,             // indicates that an RTS packet has to be sent
          input  wire        sendCTS_p,             // indicates that a CTS packet has to be sent
          input  wire        sendACK_p,             // indicates that an ACK packet has to be sent
          input  wire        sendCFEND_p,           // indicates that a CF-END packet has to be sent
          input  wire        sendBA_p,              // indicates that an Block ACK packet has to be sent
          input  wire        sendOnSIFS,            // If set, data is sent on tickSIFS else on tickSlot
          output reg         txDone_p,              // indicates the end of the transmission
          
          //$port_g TX Parameter interface
          input  wire        txParameterHDReady_p,  // Indicates if the Header Descriptor fields are usable 
          input  wire        aMPDU,                 // indicates that the current frame is an A-MPDU
          input  wire        txSingleVHTMPDU,       // Flag of single VHT MPDU
          input  wire [15:0] MPDUFrameLengthTx,     // Gives the length of the current MPDU
          input  wire  [9:0] nBlankMDelimiters,     // Indicates the number of blank MPDU delimiters that are inserted
          input  wire  [1:0] whichDescriptor,       // Indicates what kind of a descriptor this is

          //$port_g Timers Block interface
          input  wire        tickSlot,            // A pulse to indicate the end of Slot period
          input  wire        tickSIFS,            // A pulse to indicate the end of SIFS period

          //$port_g formatXXX  submodule interface
          input  wire        rtsDone_p,             // indicates that the RTS packet has been sent
          input  wire        ctsDone_p,             // indicates that the CTS packet has been sent
          input  wire        ackDone_p,             // indicates that the ACK packet has been sent
          input  wire        cfendDone_p,           // indicates that the CF-END packet has been sent
          input  wire        baDone_p,              // indicates that the BA packet has been sent
          input  wire        qosnullDone_p,         // indicates that the QoS-Null packet has been sent
          input  wire        mpduDone_p,            // indicates that the Data packet has been sent
          
          input  wire        rtsTxStart_p,          // indicates that the RTS packet starts on the MAC-PHY Interface
          input  wire        ctsTxStart_p,          // indicates that the CTS packet starts on the MAC-PHY Interface
          input  wire        ackTxStart_p,          // indicates that the ACK packet starts on the MAC-PHY Interface
          input  wire        cfendTxStart_p,        // indicates that the CF-END packet starts on the MAC-PHY Interface
          input  wire        baTxStart_p,           // indicates that the BA packet starts on the MAC-PHY Interface
          input  wire        qosnullTxStart_p,      // indicates that the QoS-Null packet starts on the MAC-PHY Interface
          input  wire        mpduTxStart_p,         // indicates that the Data packet starts on the MAC-PHY Interface

          input  wire        aMPDUDelimiterDone_p,  // indicates that the A-MPDU Delimiter has been sent
          input  wire        aMPDUPaddingDone_p,    // indicates that the padding bytes have been sent

          output wire        aMPDUPaddingStart_p,   // indicates that some pad  byte have to be added 
          output wire        aMPDUDelimiterStart_p, // indicates that the AMPDU Delimiters have to be generated
          output wire        addBlankDelimiter,     // indicates if blank delimiters shall be added
          output wire        sendMPDU_p,            // Start the transmission of a MPDU.

          //$port_g MAC-PHY IF Module interface
          input  wire        mpIfTxErr_p,           // Transmit error 
          input  wire        mpIfTxEn,              // Transmit on-going Indication
          output wire        startTx_p,             // Start Tx trigger                 
          output wire        stopTx_p,              // Stop Tx trigger                  

          //$port_g Debug interface
          output reg   [3:0] txControlMainFSMCs     // txControlMainFSM FSM Current State
                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////

//`define TX_QOSNULL


// txControlMainFSM FSM states definition
//$fsm_sd txControlMainFSM
localparam 
                 IDLE  =  4'd0,  // 
WAIT_FOR_SIFS_OR_SLOT  =  4'd1,  // 
         TX_AMPDU_DLM  =  4'd2,  // 
             TX_FRAME  =  4'd3,  // 
       WAIT_HD_TOGGLE  =  4'd4,  // 
         TX_AMPDU_PAD  =  4'd5,  // 
             TX_CFEND  =  4'd6,  // 
               TX_RTS  =  4'd7,  // 
               TX_CTS  =  4'd8,  // 
               TX_ACK  =  4'd9,  // 
              TX_BACK  =  4'd10, // 
      `ifdef TX_QOSNULL 
           TX_QOSNULL  =  4'd11, // 
      `endif // TX_QOSNULL 
          TX_WAIT_END  =  4'd12; // 



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

// txControlMainFSM FSM signals definition
reg [3:0] txControlMainFSMNs;  // txControlMainFSM FSM Next State

reg lastMPDU;
reg newHDValid; // Indicates that the new Header Descriptor is available 

wire ampduTxStart_p;

`ifdef RW_SIMU_ON
// String definition to display txControlMainFSM current state
reg [21*8:0] txControlMainFSMCs_str;
`endif // RW_SIMU_ON


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// txControlMainFSM FSM Current State Logic 
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txControlMainFSMCs <= IDLE; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    txControlMainFSMCs <= IDLE; 
  else
    txControlMainFSMCs <= txControlMainFSMNs; 
end



// txControlMainFSM FSM Next State Logic.
always @* 
begin
  if (mpIfTxErr_p && (txControlMainFSMCs != IDLE))
    txControlMainFSMNs = TX_WAIT_END; 
  else
  begin
    case(txControlMainFSMCs)

      IDLE:
        //$fsm_s In IDLE state, the state machine waits for a trigger from the MAC Controller to launch the 
        //Transmission process from the TX FIFO or by generating a protection framem, or a CF-END or a 
        //response frame.
        
        case ({sendRTS_p, sendCTS_p, sendACK_p, sendCFEND_p, sendBA_p, sendData_p})
          6'b100000 : 
            //$fsm_t When sendRTS_p is received, the state machine goes to TX_RTS state
            txControlMainFSMNs = TX_RTS; 
          6'b010000 : 
            //$fsm_t When sendCTS_p is received, the state machine goes to TX_CTS state
            txControlMainFSMNs = TX_CTS; 
          6'b001000 : 
            //$fsm_t When sendACK_p is received, the state machine goes to TX_ACK state
            txControlMainFSMNs = TX_ACK; 
          6'b000100 : 
            //$fsm_t When sendCFEND_p is received, the state machine goes to TX_CFEND state
            txControlMainFSMNs = TX_CFEND; 
          6'b000010 : 
            //$fsm_t When sendBA_p is received, the state machine goes to TX_BA state
            txControlMainFSMNs = TX_BACK; 
          6'b000001 :
            begin 
              if (aMPDU)
                //$fsm_t When sendData_p is received and the frame is an A-MPDU, the state machine goes to WAIT_FOR_SIFS_OR_SLOT state
                txControlMainFSMNs = WAIT_FOR_SIFS_OR_SLOT; 
              else  
                //$fsm_t When sendData_p is received and the frame is a singleton MPDU, the state machine goes to TX_FRAME state
                txControlMainFSMNs = TX_FRAME; 
            end  
          default :
            //$fsm_t While no tx trigger is received, the state machine stays in IDLE state
            txControlMainFSMNs = IDLE;
        endcase    

      WAIT_FOR_SIFS_OR_SLOT:
        //$fsm_s In case on A-MPDU, the state machines waits in WAIT_FOR_SIFS_OR_SLOT until the Slot or SIFS boundary.
        if ((sendOnSIFS && tickSIFS) || tickSlot) 
          if (txSingleVHTMPDU)
            //$fsm_t When tickSlot_p or tickSIFS in case of sendOnSIFS mode is received and the transmission is a singletonVHTMPDU, 
            // the state machine goes directly to TX_AMPDU_DLM state (because the HD is already present)
            txControlMainFSMNs = TX_AMPDU_DLM; 
          else
            //$fsm_t When tickSlot_p or tickSIFS in case of sendOnSIFS mode is received and AMPDU, the state machine goes to
            // WAIT_HD_TOGGLE state to wait for the availability of the 1st MDPU THD information 
            txControlMainFSMNs = WAIT_HD_TOGGLE; 
        else
          //$fsm_t While no Slot/SIFS boundary indication is received, the state machine stays in WAIT_FOR_SIFS_OR_SLOT state
          txControlMainFSMNs = WAIT_FOR_SIFS_OR_SLOT;

      WAIT_HD_TOGGLE:
        //$fsm_s In WAIT_HD_TOGGLE state, the state machine waits for the availability of the next Header Descriptor from txParametersCache.
        if (newHDValid) 
          //$fsm_t When newHDValid is received meaning that the new Header Descriptor is available, the state machine goes to TX_AMPDU_DLM state
          txControlMainFSMNs = TX_AMPDU_DLM; 
        else
          //$fsm_t While newHDValid is not received, the state machine stays in WAIT_HD_TOGGLE state
          txControlMainFSMNs = WAIT_HD_TOGGLE;


      TX_AMPDU_DLM:
        //$fsm_s In TX_AMPDU_DLM state, the state machine launches the AMPDU delimiter generation and waits until its completion.
        if (aMPDUDelimiterDone_p) 
          //$fsm_t When aMPDUDelimiterDone_p is received meaning that the AMPDU delimiter has been completely transmitted to 
          //the MAC-PHY Interface, the state machine goes to TX_FRAME state
          txControlMainFSMNs = TX_FRAME; 
        else
          //$fsm_t While aMPDUDelimiterDone_p is not received, the state machine stays in TX_AMPDU_DLM state
          txControlMainFSMNs = TX_AMPDU_DLM;

      TX_FRAME:
        //$fsm_s In TX_FRAME state, the state machine launches the DATA frame transmission from the TX FIFO and waits until its completion.
        if (mpduDone_p)
        begin
          if (!aMPDU)
            //$fsm_t When mpduDone_p is received and the frame was not an A-MPDU, the state machine goes back to IDLE state.
            txControlMainFSMNs = TX_WAIT_END; 
          else
          begin
            if (MPDUFrameLengthTx[1:0] != 2'b0)
              //$fsm_t When mpduDone_p is received and the MPDU length is not a multiple of 4, 
              // the state machine goes to TX_AMPDU_PAD state to add the padding bytes.
              txControlMainFSMNs = TX_AMPDU_PAD; 
            else
            begin
              if (lastMPDU)
                //$fsm_t When mpduDone_p is received and the MPDU length is a multiple of 4 and 
                // the transmitted MPDU was the last one, the state machine goes back to IDLE state.
                txControlMainFSMNs = TX_WAIT_END; 
              else  
                //$fsm_t When mpduDone_p is received and the MPDU lenght is a multiple of 4 and 
                // the transmitted MPDU was not the last one, the state machine goes back to WAIT_HD_TOGGLE state.
                txControlMainFSMNs = WAIT_HD_TOGGLE; 
            end    
          end
        end
        else
          //$fsm_t While mpduDone_p is not received meaning that the MPDU transmission is not completed yet, 
          //the state machine stays in TX_FRAME state.
          txControlMainFSMNs = TX_FRAME;

      TX_AMPDU_PAD:
        //$fsm_s In TX_AMPDU_PAD state, the state machine launches the MPDU PADDING generation and waits until its completion.
        if (aMPDUPaddingDone_p) 
            if (lastMPDU)
              //$fsm_t When aMPDUPaddingDone_p is received and the MPDU length is a multiple of 4 and 
              // the transmitted MPDU was the last one, the state machine goes back to IDLE state.
              txControlMainFSMNs = TX_WAIT_END; 
            else  
              //$fsm_t When aMPDUPaddingDone_p is received and the MPDU lenght is a multiple of 4 and 
              // the transmitted MPDU was not the last one, the state machine goes back to WAIT_HD_TOGGLE state.
              txControlMainFSMNs = WAIT_HD_TOGGLE; 
        else
          //$fsm_t While aMPDUPaddingDone_p is not received, the state machine stays in TX_AMPDU_PAD state
          txControlMainFSMNs = TX_AMPDU_PAD;

      TX_CFEND:
        //$fsm_s In TX_CFEND state, the state machine launches the CF-END frame generation and waits 
        //until its complete transmission.
        if (cfendDone_p) 
          //$fsm_t When cfendDone_p is received, the state machine goes back to IDLE state
          txControlMainFSMNs = TX_WAIT_END;
        else
          //$fsm_t While cfendDone_p is not received, the state machine stays in TX_CFEND state
          txControlMainFSMNs = TX_CFEND;

      TX_RTS:
        //$fsm_s In TX_RTS state, the state machine launches the RTS frame generation and waits 
        //until its complete transmission.
        if (rtsDone_p) 
          //$fsm_t When rtsDone_p is received, the state machine goes back to IDLE state
          txControlMainFSMNs = TX_WAIT_END;
        else
          //$fsm_t While rtsDone_p is not received, the state machine stays in TX_RTS state
          txControlMainFSMNs = TX_RTS;

      TX_CTS:
        //$fsm_s In TX_CTS state, the state machine launches the CTS frame generation and waits 
        //until its complete transmission.
        if (ctsDone_p) 
          //$fsm_t When ctsDone_p is received, the state machine goes back to IDLE state
          txControlMainFSMNs = TX_WAIT_END; 
        else
          //$fsm_t While ctsDone_p is not received, the state machine stays in TX_CTS state
          txControlMainFSMNs = TX_CTS;

      TX_ACK:
        //$fsm_s In TX_ACK state, the state machine launches the ACK frame generation and waits 
        //until its complete transmission.
        if (ackDone_p) 
          //$fsm_t When ackDone_p is received, the state machine goes back to IDLE state
          txControlMainFSMNs = TX_WAIT_END; 
        else
          //$fsm_t While ackDone_p is not received, the state machine stays in TX_ACK state
          txControlMainFSMNs = TX_ACK;

      TX_BACK:
        //$fsm_s In TX_BACK state, the state machine launches the BLOCK ACK frame generation and waits 
        //until its complete transmission.
        if (baDone_p) 
          //$fsm_t When baDone_p is received, the state machine goes back to IDLE state
          txControlMainFSMNs = TX_WAIT_END; 
        else
          //$fsm_t While baDone_p is not received, the state machine stays in TX_BACK state
          txControlMainFSMNs = TX_BACK;

    `ifdef TX_QOSNULL 
      TX_QOSNULL:
        //$fsm_s In TX_QOSNULL state, the state machine launches the QoS Null frame generation and waits 
        //until its complete transmission.
        if (qosnullDone_p) 
          //$fsm_t When qosnullDone_p is received, the state machine goes back to IDLE state
          txControlMainFSMNs = TX_WAIT_END; 
        else
          //$fsm_t While qosnullDone_p is not received, the state machine stays in TX_QOSNULL state
          txControlMainFSMNs = TX_QOSNULL;
    `endif // TX_QOSNULL 

      TX_WAIT_END:
        //$fsm_s In TX_WAIT_END state, the state machine waits for the end of the transmission on the MAC-PHY Interface.
        if (!mpIfTxEn) 
          //$fsm_t When mpIfTxEn is low meaning that the transmission is finished at 
          //the MAC-PHY Interface, the state machine goes to IDLE state
          txControlMainFSMNs = IDLE; 
        else
          //$fsm_t While mpIfTxEn is set, the state machine stays in TX_WAIT_END state
          txControlMainFSMNs = TX_WAIT_END;

       // Disable coverage on the default state because it cannot be reached.
       // pragma coverage block = off 
       default:   
          txControlMainFSMNs = IDLE; 
       // pragma coverage block = on 
    endcase
  end  
end



// 
assign startTx_p = ctsTxStart_p || rtsTxStart_p || ackTxStart_p || baTxStart_p || cfendTxStart_p || mpduTxStart_p || ampduTxStart_p;

// In case of underrun detected by the MAC, the txReq is deasserted.
assign stopTx_p  = mpIfTxErr_p;

assign ampduTxStart_p = ((txControlMainFSMNs == TX_AMPDU_DLM) && ((txControlMainFSMCs == WAIT_HD_TOGGLE) && (whichDescriptor == 2'b01) || (txControlMainFSMCs == WAIT_FOR_SIFS_OR_SLOT))) ? 1'b1 : 1'b0;


assign aMPDUPaddingStart_p   = (txControlMainFSMNs == TX_AMPDU_PAD) ? 1'b1 : 1'b0;
assign aMPDUDelimiterStart_p = (txControlMainFSMNs == TX_AMPDU_DLM) ? 1'b1 : 1'b0;
assign sendMPDU_p            = ((txControlMainFSMCs != TX_FRAME) && (txControlMainFSMNs == TX_FRAME)) ? 1'b1 : 1'b0;

//assign addBlankDelimiter     = ((txControlMainFSMNs == TX_AMPDU_DLM) && (whichDescriptor != 2'b01) && (nBlankMDelimiters != 10'b0)) ? 1'b1 : 1'b0;
assign addBlankDelimiter     = ((txControlMainFSMNs == TX_AMPDU_DLM) && (nBlankMDelimiters != 10'b0)) ? 1'b1 : 1'b0;

// newHDValid indication generation
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    newHDValid <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    newHDValid <= 1'b0; 
  else
    if ((sendData_p && aMPDU && !txSingleVHTMPDU)  || sendMPDU_p || mpduDone_p)
      newHDValid <= 1'b0;
    else if(txParameterHDReady_p)
      newHDValid <= 1'b1;
end


// LastMPDU indication generation
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    lastMPDU <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    lastMPDU <= 1'b0; 
  else
    if (sendMPDU_p)
    begin
      if (aMPDU && ((whichDescriptor[1:0] == 2'b11) || txSingleVHTMPDU))
        lastMPDU <= 1'b1; 
      else  
        lastMPDU <= 1'b0; 
    end    
end

// txDone_p indication generation
always @ (posedge macCoreTxClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    txDone_p <= 1'b0; 
  else if (macCoreTxClkSoftRst_n == 1'b0)  // Synchronous Reset
    txDone_p <= 1'b0; 
  else
    if ((mpIfTxEn == 1'b0) && (txControlMainFSMCs == TX_WAIT_END))
      txDone_p <= 1'b1; 
    else  
      txDone_p <= 1'b0; 
end




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage the RW_SIMU_ON part because this code is not functional but 
// here to ease the simulation
// pragma coverage block = off 

// txControlMainFSM FSM states displayed in a string to easy simulation and debug
always @*
begin
  case (txControlMainFSMCs)
                 IDLE  :  txControlMainFSMCs_str = {"IDLE"};
WAIT_FOR_SIFS_OR_SLOT  :  txControlMainFSMCs_str = {"WAIT_FOR_SIFS_OR_SLOT"};
       WAIT_HD_TOGGLE  :  txControlMainFSMCs_str = {"WAIT_HD_TOGGLE"};
         TX_AMPDU_DLM  :  txControlMainFSMCs_str = {"TX_AMPDU_DLM"};
             TX_FRAME  :  txControlMainFSMCs_str = {"TX_FRAME"};
         TX_AMPDU_PAD  :  txControlMainFSMCs_str = {"TX_AMPDU_PAD"};
             TX_CFEND  :  txControlMainFSMCs_str = {"TX_CFEND"};
               TX_RTS  :  txControlMainFSMCs_str = {"TX_RTS"};
               TX_CTS  :  txControlMainFSMCs_str = {"TX_CTS"};
               TX_ACK  :  txControlMainFSMCs_str = {"TX_ACK"};
              TX_BACK  :  txControlMainFSMCs_str = {"TX_BACK"};
         `ifdef TX_QOSNULL 
           TX_QOSNULL  :  txControlMainFSMCs_str = {"TX_QOSNULL"};
         `endif // TX_QOSNULL 
           TX_WAIT_END :  txControlMainFSMCs_str = {"TX_WAIT_END"};
              default  :  txControlMainFSMCs_str = {"XXX"};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON

// System Verilog Assertions
////////////////////////////

`ifdef RW_ASSERT_ON
//$rw_sva This cover point checks if we are transmitting an aMPDU
countIfAMPDUFrame: cover property (@(posedge macCoreTxClk) (mpduDone_p && lastMPDU));



`endif // RW_ASSERT_ON



endmodule
                 
