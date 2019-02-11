//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $RCSmodulefile   :
// $Author          :
// Company          :
//----------------------------------------------------------------------------
// $Revision:
// $Date:
// $State:
// $Locker:
// ---------------------------------------------------------------------------
// Dependencies     :
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
//
//
//
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module ccmCntl (
  // $port_g Clock & Reset
  input   wire            ccmp_clk,               // CCMP Clock
  input   wire            ccmp_hardrst_n,         // Hard Reset
  input   wire            ccmp_softrst_n,         // Soft Reset

  // $port_g CCMP AES MIC
  input   wire            aes_mic_out_valid,      // Pulse valid when aes mic data out is ready
  input   wire    [127:0] aes_mic_out,            // AES mic data out

  output  wire            aes_mic_in_valid,       // Pulse valid when aes mic data in is ready
  output  wire    [127:0] aes_mic_in,             // AES mic data in

  // $port_g CCMP AES CRT
  input   wire            aes_crt_out_valid,      // Pulse valid when aes crt data out is ready
  input   wire    [127:0] aes_crt_out,            // AES crt data out

  output  wire            aes_crt_in_valid,       // Pulse valid when aes crt data in is ready
  output  wire    [127:0] aes_crt_in,             // AES crt data in

  // $port_g CCMP DATA and CONTROL
  input   wire            ccmp_tx_nrx,            // Indicate if CCMP is in tx or rx mode (tx = 1'b1, rx = 1'b0)
  input   wire            ccmp_init_p,            // Pulse to start CCMP encryption or decryption
  input   wire            ccmp_aadValid,          // Level signal to indicate the AAD validity until the pulse loadAAD2 raised
  input   wire            ccmp_outRegEmpty,       // Level signal when low then stop trigerring aes_mic_in_valid and aes_crt_in_valid until high again
  input   wire            ccmp_rxError_p,         // Pulse to indicate rx Error
  input   wire            ccmp_txError_p,         // Pulse to indicate tx Error
  input   wire            ccmp_lastpayload,       // Pulse to indicate last data payload has been loaded into ccmp_data_in
  input   wire            ccmp_micend,            // Pulse to indicate the rx MIC is in ccmp_data_in

  input   wire    [255:0] ccmp_aad,               // AAD value (valid only when ccmp_aadValid is high)
  input   wire    [103:0] ccmp_nonce,             // NONCE value
  input   wire     [15:0] ccmp_payloadLen,        // Payload length of the full frame
  input   wire    [127:0] ccmp_data_out_mask,     // Data out mask is used to keep only the rights bytes from the xor between  ccmp_data_in and aes_crt_out

  output  wire            ccmp_loadAAD2,          // Pulse to indicate that the ADD2 is laoded into aes_mic_in
  output  wire            ccmp_loadMSG,           // Pulse to indicate that the message in ccmp_data_in has been used and can now be rewritten
  output  wire            ccmp_isIdle,            // Indicate CCMP is in IDLE state
  input   wire            ccmp_data_in_valid,     // Level signal to indicate that the data in ccmp_data_in has been shifted in

  input   wire    [127:0] ccmp_data_in,           // Plain/Encrypted data in
  output  wire    [127:0] ccmp_data_out,          // Plain/Encrypted data out

  output  wire            ccmp_mic_failed,        // Pulse for MIC failed (at the end of rx in mic comparison or error detected)
  output  wire            ccmp_mic_passed,        // Pulse for MIC passed (at the end of rx in mic comparison)
  output  wire            ccmp_mic_valid,         // Pulse to indicate the validity of ccmp_mic calculated for tx encrypt frame
  output  wire     [63:0] ccmp_mic,               // MIC value
  output  wire      [3:0] ccmp_cntlCS             // ccmCntl Current State
  );

  // State Machine
  //$fsm_sd currentState
  localparam 
    IDLE      = 3'd0,
    INITB0    = 3'd1,
    INITAAD1  = 3'd2,
    INITAAD2  = 3'd3,
    MSG       = 3'd4,
    MIC       = 3'd5,
    MIC_CHECK = 3'd6,
    ERROR     = 3'd7;

  // Registers
  reg         [2:0] currentState;
  reg               aes_mic_done;
  reg               aes_crt_done;
  reg        [15:0] counter;
  reg               ccmp_lastpayload_detected;

  // Wires
  reg         [2:0] nextState;
  reg       [127:0] aes_mic_in_reg;
  reg       [127:0] aes_crt_in_reg;

  reg       [127:0] ccmp_data_out_reg;
  reg        [63:0] ccmp_mic_reg;
  reg        [63:0] aes_crt_0_reg;

  wire              ccmp_enable;
  wire              ccmp_error;

  // Debug purpose only
  `ifdef RW_SIMU_ON
  reg       [20*8:0] currentState_str;
  reg       [20*8:0] nextState_str;
  `endif

  // Debug
  assign ccmp_cntlCS     = {ccmp_init_p,currentState[2:0]};

  // Mic Fail and Pass
  assign ccmp_mic_passed = (currentState == MIC_CHECK) && (nextState == IDLE) && (ccmp_mic == ccmp_data_in[63:0]);
  assign ccmp_mic_failed = ((currentState == MIC_CHECK) && (nextState == IDLE) && (ccmp_mic_passed == 1'b0)) || ((currentState == ERROR) && (ccmp_tx_nrx == 1'b0));

  // IDLE flag
  assign ccmp_isIdle = ((currentState == IDLE) && (nextState == IDLE));

  // Internal wires logics
  // Generates Error flag if received rx/tx error pulse from Mac Controller
  assign  ccmp_error  = ((ccmp_tx_nrx == 1'b0) && (ccmp_rxError_p == 1'b1))                                                           || // error pulse from rx controller
                        ((ccmp_tx_nrx == 1'b0) && (currentState   != IDLE) && (currentState   != ERROR) && (ccmp_payloadLen == 16'h0))|| // error from rx length
                        ((ccmp_tx_nrx == 1'b1) && (ccmp_txError_p == 1'b1));                                                             // error from tx controller

  // Generates Automatic Clockgating signal enable (useful to gate all the FFs' clk when the signal is low) :
  // ccmp_enable is high when the state is out of IDLE or if it is going out of IDLE
  assign  ccmp_enable = (currentState == IDLE && nextState != IDLE) || (currentState != IDLE);

  // current state :
  // Takes the value of nextState when ccmp_enable is high
  always @(posedge ccmp_clk, negedge ccmp_hardrst_n)
  begin
    if(ccmp_hardrst_n == 1'b0)
    begin
      currentState <= IDLE;
    end
    else if(ccmp_softrst_n == 1'b0 )
    begin
      currentState <= IDLE;
    end
    else if(ccmp_enable) 
    begin
      currentState <= nextState;
    end
  end

  // next state :
  // nextState changes according to the currentState and the right condition.
  always @(*)
  begin
    //when not in ERROR state, and ccmp_error rise, then nextState goes to ERROR.
    if((currentState != ERROR) && (currentState != IDLE) && (ccmp_error == 1'b1))
    begin
      nextState = ERROR;
    end
    //else ccmp_error can be ignored
    else
    begin
      case(currentState)
        IDLE    :
        begin
          //$fsm_s In IDLE, the state waits for the inti pulse
          if(ccmp_init_p == 1'b1)
            //$fsm_t If init pulse is received then the state goes to INITB0 state
            nextState = INITB0;
          else
            //$fsm_t While no init pulse, the state stays in IDLE state
            nextState = IDLE;
        end

        INITB0  :
        begin
          //$fsm_s In INITB0, the state waits for the block aes mic computation, and waits also for the ADD data to be available
          if((aes_mic_done == 1'b1) && (ccmp_aadValid == 1'b1))
            //$fsm_t If done b0 and aadValid rise, then the state goes to INITAAD1 state
            nextState = INITAAD1;
          else
            //$fsm_t While aes mic computation is not done or ADD is not valid, the state stays in INITB0 state
            nextState = INITB0;
        end

        INITAAD1:
        begin
          //$fsm_s In INITAAD1, the state wait for the block aes mic computation
          if(aes_mic_done == 1'b1)
            //$fsm_t If done aad1 then compute aad2, the state goes to INITAAD2 state
            nextState = INITAAD2;
          else
            //$fsm_t While computaion of ADD1 is not done, the state waits in INITAAD1 state
            nextState = INITAAD1;
        end

        INITAAD2:
        begin
          //$fsm_s In INITAAD2, the state wait for the block aes mic computation
          if((aes_mic_done == 1'b1) && (ccmp_data_in_valid == 1'b1))
            //$fsm_t If done aad2 and the data in is valid then compute first message, the state goes to MSG state
            nextState = MSG;
          else
            //$fsm_t While aad2 not done or the data in is not valid, the state waits in INITAAD2 state
            nextState = INITAAD2;
        end

        MSG     :
        begin
          //$fsm_s In MSG, the state wait for the last block comptutation
          if((aes_mic_done == 1'b1) && (aes_crt_done == 1'b1) && (ccmp_lastpayload_detected == 1'b1))
            //$fsm_t If the last block of data is encrypted/decrypted, the state goes to MIC state
            nextState = MIC;
          else
            //$fsm_t While there are still payload to encrypt/decrypt, the state stays in MSG state
            nextState = MSG;
        end

        MIC     :
        begin
          //$fsm_s In MIC, the state wait for the mic shifted out in Tx
          if(ccmp_tx_nrx && ccmp_outRegEmpty)
            //$fsm_t When Tx and mic shifted out, the state goes to IDLE state
            nextState = IDLE;
          else if(!ccmp_tx_nrx)
            //$fsm_t When Rx, the state goes to MIC_CHECK state
            nextState = MIC_CHECK;
          else
            //$fsm_t While Tx and mic not shifted out, the state stays in MIC state
            nextState = MIC;
        end

        MIC_CHECK:
        begin
          //$fsm_s In MIC_CHECK, the state wait for mic computation end
           if(ccmp_micend == 1'b1)
            //$fsm_t When mic comparison done, the state goes to IDLE state
            nextState = IDLE;
          else
            //$fsm_t While the mic is not compared, the state stays in MIC_CHECK state
            nextState = MIC_CHECK;
        end

        ERROR   :
        begin
          //$fsm_s In ERROR, the state wait for one clock cycle
          
          //$fsm_t After one clock cycle, the state goes to IDLE state
          nextState = IDLE;
        end

        default :
        begin
          nextState = IDLE;
        end 
      endcase
    end
  end

  // output pulse loadAAD2 to start getting the first data in
  assign  ccmp_loadAAD2    =  ((currentState == INITAAD1) && (nextState == INITAAD2));

  // output pulse loadMSG to start pushing data out and get the next data in
  assign  ccmp_loadMSG     =  ((currentState == INITAAD2) && (nextState == MSG))                                                    ||
                              ((currentState == MSG)      && (nextState == MSG) && (aes_mic_done == 1'b1) && (aes_crt_done == 1'b1) && (ccmp_data_in_valid == 1'b1) && (ccmp_outRegEmpty == 1'b1));

  // ouput pulse to trigger aes mic block only when needed 
  assign  aes_mic_in_valid =  ((currentState == IDLE)     && (nextState == INITB0))                                                 ||
                              ((currentState == INITB0)   && (nextState == INITAAD1))                                               ||
                              ((currentState == INITAAD1) && (nextState == INITAAD2))                                               ||
                              ((currentState == INITAAD2) && (nextState == MSG))                                                    ||
                              ((currentState == MSG)      && (nextState == MSG) && (aes_mic_done == 1'b1) && (aes_crt_done == 1'b1) && (ccmp_data_in_valid == 1'b1) && (ccmp_outRegEmpty == 1'b1));

  // output pulse to trigger aes crt block only when needed
  assign  aes_crt_in_valid =  ((currentState == INITAAD1) && (nextState == INITAAD2))                                               ||
                              ((currentState == INITAAD2) && (nextState == MSG))                                                    ||
                              ((currentState == INITB0)   && (nextState == INITAAD1))                                               ||
                              ((currentState == MSG)      && (nextState == MSG) && (aes_mic_done == 1'b1) && (aes_crt_done == 1'b1) && (ccmp_data_in_valid == 1'b1) && (ccmp_outRegEmpty == 1'b1));

  // internal done flags used to trigger mic and crt aes
  always @(posedge ccmp_clk, negedge ccmp_hardrst_n)
  begin
    if(ccmp_hardrst_n == 1'b0)
    begin
      aes_mic_done  <= 1'b0;
      aes_crt_done  <= 1'b0;
    end
    else if(ccmp_softrst_n == 1'b0 )
    begin
      aes_mic_done  <= 1'b0;
      aes_crt_done  <= 1'b0;
    end
    else if(ccmp_enable) 
    begin
      if(aes_mic_in_valid == 1'b1)
        aes_mic_done  <= 1'b0;
      else if(aes_mic_out_valid == 1'b1)
        aes_mic_done  <= 1'b1;
      else if(nextState == IDLE)
        aes_mic_done  <= 1'b0;

      if(aes_crt_in_valid == 1'b1)
        aes_crt_done  <= 1'b0;
      else if(aes_crt_out_valid == 1'b1)
        aes_crt_done  <= 1'b1;
      else if(nextState == IDLE)
        aes_crt_done  <= 1'b0;
    end
  end

  // assign output wires
  assign  ccmp_data_out = ccmp_data_out_reg;
  assign  ccmp_mic      = ccmp_mic_reg;
  assign  ccmp_mic_valid= ((currentState == MIC) && (nextState == IDLE));

  // generates mic output and data out
  always @(*)
  begin
    ccmp_mic_reg = aes_crt_0_reg[63:0] ^ aes_mic_out[63:0];
    if((nextState == MSG) && (aes_mic_in_valid == 1'b1)) 
      ccmp_data_out_reg  = (aes_crt_out ^ ccmp_data_in) & ccmp_data_out_mask;
    else
      ccmp_data_out_reg  = aes_crt_out;
  end

  // assign output for aes mic data in
  assign aes_mic_in = aes_mic_in_reg;

  // generate aes mic data in
  always @(*)
  begin
    if     ((currentState == IDLE)     && (nextState == INITB0))
    begin
      aes_mic_in_reg = {ccmp_payloadLen[7:0],ccmp_payloadLen[15:8],ccmp_nonce[103:0], 8'h59};
    end
    else if((currentState == INITB0)   && (nextState == INITAAD1))
    begin
      aes_mic_in_reg = ccmp_aad[255:128] ^ aes_mic_out;
    end
    else if((currentState == INITAAD1) && (nextState == INITAAD2))
    begin
      aes_mic_in_reg = ccmp_aad[127:0]   ^ aes_mic_out;
    end
    else
    begin
      if(ccmp_tx_nrx == 1'b1)
        aes_mic_in_reg = ccmp_data_in   ^ aes_mic_out;
      else
        aes_mic_in_reg = ccmp_data_out  ^ aes_mic_out;
    end
  end

  // assign output for aes crt data in
  assign aes_crt_in = aes_crt_in_reg;

  // generate aes crt data in
  always @(*)
  begin
    aes_crt_in_reg = {counter[7:0], counter[15:8], ccmp_nonce, 8'h01};
  end

  // generate counter used for aes crt data in
  always @(posedge ccmp_clk, negedge ccmp_hardrst_n)
  begin
    if(ccmp_hardrst_n == 1'b0)
    begin
      counter  <= 16'h0;
    end
    else if(ccmp_softrst_n == 1'b0 )
    begin
      counter  <= 16'h0;
    end
    else if(ccmp_enable) 
    begin
      if(aes_crt_in_valid)
        counter <= counter + 16'd1;
      else if(nextState == INITB0)
        counter <= 16'h0;
    end
  end

  // Caputure de crt 0 result for mic gen
  always @(posedge ccmp_clk, negedge ccmp_hardrst_n)
  begin
    if(ccmp_hardrst_n == 1'b0)
    begin
      aes_crt_0_reg  <= 64'h0;
    end
    else if(ccmp_softrst_n == 1'b0 )
    begin
      aes_crt_0_reg  <= 64'h0;
    end
    else if(ccmp_enable) 
    begin
      if(aes_crt_done && currentState == INITAAD1)
        aes_crt_0_reg <= aes_crt_out[63:0];
      else if(nextState == INITB0)
        aes_crt_0_reg  <= 64'h0;
    end
  end


  // generate last payload detection (memorize the pulse ccmp_lastpayload)
  always @(posedge ccmp_clk, negedge ccmp_hardrst_n)
  begin
    if(ccmp_hardrst_n == 1'b0)
    begin
      ccmp_lastpayload_detected  <= 1'b0;
    end
    else if(ccmp_softrst_n == 1'b0 )
    begin
      ccmp_lastpayload_detected  <= 1'b0;
    end
    else if(ccmp_enable) 
    begin
      if(ccmp_lastpayload)
        ccmp_lastpayload_detected <= 1'b1;
      else if(nextState == IDLE)
        ccmp_lastpayload_detected <= 1'b0;
    end
  end

  // debug purpose only
  `ifdef RW_SIMU_ON
  // state FSM states displayed in a string to easy simulation and debug
  always @*
  begin
    case (currentState)
      IDLE     :  currentState_str = {"IDLE"};
      INITB0   :  currentState_str = {"INITB0"};
      INITAAD1 :  currentState_str = {"INITAAD1"};
      INITAAD2 :  currentState_str = {"INITAAD2"};
      MSG      :  currentState_str = {"MSG"};
      MIC      :  currentState_str = {"MIC"};
      MIC_CHECK:  currentState_str = {"MIC_CHECK"};
      ERROR    :  currentState_str = {"ERROR"};
      default  :  currentState_str = {"XXX"};
    endcase
    case (nextState)
      IDLE     :  nextState_str = {"IDLE"};
      INITB0   :  nextState_str = {"INITB0"};
      INITAAD1 :  nextState_str = {"INITAAD1"};
      INITAAD2 :  nextState_str = {"INITAAD2"};
      MSG      :  nextState_str = {"MSG"};
      MIC      :  nextState_str = {"MIC"};
      MIC_CHECK:  nextState_str = {"MIC_CHECK"};
      ERROR    :  nextState_str = {"ERROR"};
      default  :  nextState_str = {"XXX"};
    endcase
  end
  `endif // RW_SIMU_ON
endmodule  

//------------------- END OF FILE ----------------//

