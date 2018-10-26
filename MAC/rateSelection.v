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
// Description      : Select the rate according to the standard for 
//                    Data/managment frames, control response, control frame 
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
// -------------------------------------------------------------------------
//                                                                          
// 
// 
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

module rateSelection( 
          //$port_g Clock and Reset interface
          input  wire        macCoreClk,            // MAC Core Transmit Clock
          input  wire        macCoreClkHardRst_n,   // Hard Reset of the MAC Core Clock domain 
                                                    // active low
          input  wire        macCoreClkSoftRst_n,   // Soft Reset of the MAC Core Clock domain 
                                                    // active low

          //$port_g Interface with the Tx Parameters Cache
          input  wire  [2:0] formatModProtTx,        // Format and Modulation of Protection frame for Transmission
                                                     //   3'b000: NON-HT
                                                     //   3'b001: NON-HT-DUP-OFDM
                                                     //   3'b010: HT-MF
                                                     //   3'b011: HT-GF
                                                     //   3'b100: VHT
          input  wire  [2:0] formatModTx,            // Format and Modulation of PPDU for Transmission
                                                     // Same coding than formatModProtTx
          input  wire  [6:0] mcsIndex0Tx,           // MCS Index 0 of PPDU for Transmission
          input  wire  [1:0] bwDataTx,              // BW of PPDU for Transmission

          input  wire  [1:0] stbcTx,                // STBC for Transmission
          input  wire        lowRateRetry,          // Lower Rate on Retries

          //$port_g Interface with Rx Controller
          input  wire  [6:0] rxMCS,                 // MCS Index of received frame
          input  wire  [3:0] rxLegRate,             // Legacy rate of received frame
          input  wire  [2:0] rxFormatMod,           // Modulation format of received frame
          input  wire  [1:0] rxSTBC,                // STBC of received frame

          //$port_g Interface with the CSReg
          input  wire [11:0] bssBasicRateSet,       // BSS Basic Rate Set
          input  wire [15:0] bssBasicHTMCSSetEM,    // BSS Basic HT MCS Set for Equal Modulation
          input  wire  [5:0] bssBasicHTMCSSetUM,    // BSS Basic HT MCS Set for Unequal Modulation
          input  wire [15:0] bssBasicVHTMCSSet,     // BSS Basic VHT MCS Set
          input  wire  [6:0] basicSTBCMCS,          // Basic MCS for STBC modulation
          input  wire        dualCTSProt,           // Dual-CTS Protection
          input  wire        ap,                    // Indicates the type of device (0: STA, 1: AP)

          //$port_g Interface with macControllerTX
          input  wire        rateUpdateTxC_p,       // Request from the macControllerTx to update the rate
          input  wire  [6:0] mcsIndex0Prot,         // MCS Index 0 of Protection frame for Transmission

          //$port_g Interface with macControllerRX
          input  wire        rateUpdateRxC_p,       // Request from the macControllerTx to update the rate

          //$port_g Interface with macController
          input  wire        txExchangeEnabled,     // Enables the TX frame exchange
          output reg         rateUpdateDone_p,      // Indicates the completion of the rate processing
          output reg   [3:0] rxLegRateConv,         // Converted rxLegRate
          output reg   [6:0] mcsData,               // MCS Index for Data frame
          output reg   [3:0] legRateData,           // Legacy Rate Index for Data frame
          output wire  [6:0] mcsCFEND,              // MCS Index for CF-END
          output reg   [3:0] legRateCFEND,          // Legacy Rate Index for CF-END
          output reg   [6:0] mcsPROT,               // MCS Index for PROT frame
          output reg   [3:0] legRatePROT,           // Legacy Rate Index for PROT frame
          output reg   [6:0] mcsRESP,               // MCS Index for response frame
          output reg   [3:0] legRateRESP            // Legacy Rate Index for response frame

                 );


//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

reg  [6:0] mcsRESP_comb;
reg  [3:0] legRateRESP_comb;
reg  [6:0] mcsData_comb;
wire [3:0] legRateData_comb;
reg  [6:0] mcsPROT_comb;
wire [3:0] legRatePROT_comb;

reg [12:0] legRateRespSet;  // Indicates the legacy Rate of the received frame using the same format than bssBasicRateSet
reg [15:0] mcsRespSet;      // Indicates the MCS of the received frame using the same format than bssBasicHTMCSSetEM and bssBasicHTMCSSetUM
wire [15:0] mcsRespMandatorySet; // Indicates the mandatory MCS of the received frame using the same format than bssBasicHTMCSSetEM and bssBasicHTMCSSetUM

wire [2:0] formatModResp;

wire [6:0] mcsPPDU;
wire [3:0] legRatePPDU;


wire [11:0] legRateRESPCond1;
wire [15:0] mcsRESPCond1;
wire [15:0] mcsRESPCond2;
wire  [5:0] mcsRESPCond3;
wire  [9:0] mcsRESPCond4;

reg   [1:0] stbc; 


reg     started;

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Begining of Data Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////

always @(*)
begin
  // In VHT, some MCS are not allowed. As a consequence, the following logic reduces the MCS if the selected one is not allowed.
  if (formatModTx == 3'd4)
  begin
    case ({bwDataTx,mcsIndex0Tx[6:4],mcsIndex0Tx[3:0]}) // mcsIndex0Tx[6:4] = NSS - 1 and mcsIndex0Tx[3:0] = MCS
//    case ({2'b01,mcsIndex0Tx[6:4],mcsIndex0Tx[3:0]}) // mcsIndex0Tx[6:4] = NSS - 1 and mcsIndex0Tx[3:0] = MCS
      9'b00_000_1001 : mcsData_comb = 7'b000_1000;  // If BW is 20MHz and NSS = 1, MCS 9 is not allowed. So, use MCS 8  
      9'b00_001_1001 : mcsData_comb = 7'b001_1000;  // If BW is 20MHz and NSS = 2, MCS 9 is not allowed. So, use MCS 8 
      9'b00_011_1001 : mcsData_comb = 7'b011_1000;  // If BW is 20MHz and NSS = 4, MCS 9 is not allowed. So, use MCS 8
      9'b10_010_0110 : mcsData_comb = 7'b010_0101;  // If BW is 80MHz and NSS = 3, MCS 6 is not allowed. So, use MCS 5
      9'b11_010_1001 : mcsData_comb = 7'b010_1000;  // If BW is 160MHz and NSS = 3, MCS 9 is not allowed. So, use MCS 8
    default : mcsData_comb = mcsIndex0Tx[6:0];
    endcase
  end
  else
    mcsData_comb = mcsIndex0Tx[6:0];
end

// When transmitting a HT/VHT PPDU (MCS[7] = 1), the legRateData always indicates 6Mbps
assign legRateData_comb = (formatModTx[2:1] > 2'b0) ? 4'b0100 : mcsIndex0Tx[3:0];


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    mcsData     <= 7'b0; 
    legRateData <= 4'b0; 
  end  
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    mcsData     <= 7'b0; 
    legRateData <= 4'b0; 
  end  
  else
    if (rateUpdateTxC_p || rateUpdateRxC_p)
    begin
      mcsData     <= mcsData_comb; 
      legRateData <= legRateData_comb;
    end  
end

//////////////////////////////////////////////////////////////////////////////
// End of Data Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Begining of Protection Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////


// When transmitting a HT/VHT Protection frame (MCS[7] = 1), the legRatePROT always indicates 6Mbps
assign legRatePROT_comb = (formatModProtTx[2:1] > 2'b0) ? 4'b0100 : mcsPROT_comb[3:0];

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    mcsPROT     <= 7'b0; 
    legRatePROT <= 4'b0; 
  end  
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    mcsPROT     <= 7'b0; 
    legRatePROT <= 4'b0; 
  end  
  else
    begin
      // In case of VHT, some MCS, NSS and BW combination are not allowed.
      // To simplify the logic, the following decisions have been taken.
      //  1- Protection frame are not transmitted with MCS 8 or 9
      //  2- Protection frame with NSS = 3 and MCS = 6 is automatically changed by NSS = 3 and MCS = 5
      if (formatModProtTx == 3'd4)
      begin
        if (mcsPROT_comb[3] == 1'b1)
          // MCS 8 or 9 for protection is avoided.
          // reduce to MCS 7
          mcsPROT     <= {mcsPROT_comb[6:4],4'd7};
        else if (mcsPROT_comb[6:0] == 7'b010_0110)
          // MCS 6 with NSS = 3 for protection is avoided.
          // reduce to MCS 5
          mcsPROT     <= 7'b010_0101;
        else
          mcsPROT     <= mcsPROT_comb[6:0];
      end    
      else    
        mcsPROT     <= mcsPROT_comb[6:0];
      
      legRatePROT <= legRatePROT_comb;
    end
end

always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    rateUpdateDone_p  <= 1'b0;
  end  
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    rateUpdateDone_p  <= 1'b0;
  end  
  else
  begin
    if (started || (rateUpdateTxC_p || rateUpdateRxC_p))
    begin
      rateUpdateDone_p <= 1'b1;
    end
    else if(rateUpdateDone_p)
    begin
      rateUpdateDone_p <= 1'b0;
    end
  end
end

// Launch the processing
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    started     <= 1'b0; 
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
    started     <= 1'b0; 
  else
  begin
    if (rateUpdateTxC_p || rateUpdateRxC_p)
      started     <= 1'b1; 
    if (rateUpdateDone_p)
      started     <= 1'b0; 
  end  
end

// capture STBC configuration
always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
    stbc     <= 2'b0; 
  else if (rateUpdateTxC_p)
    stbc     <= stbcTx; 
  else if (rateUpdateRxC_p)
    stbc     <= rxSTBC; 
end

// Assign mcsPROT_comb based on number of retry and the different computation results.
always @*
begin
  // If the frame eliciting the response was an STBC frame and the Dual CTS Protection bit is equal to 1,
  // the CandidateMCSSet shall contain only the basic STBC MCS.
  if ((stbc != 2'b0) && dualCTSProt)
    mcsPROT_comb = basicSTBCMCS;
  else
    mcsPROT_comb = mcsIndex0Prot[6:0]; 
end  


//////////////////////////////////////////////////////////////////////////////
// End of Protection Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Begining of Response Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////
// conversion between MCS Index and legay Rate at the MAC PHY Interface
//  txLegRate is the legacy rate based on MCS Index
//  legRate is the legacy rate following the MAC-PHY If convention
//
// The following table provides the conversion rule.
//       +---------+-----+------+
//       | LegRate | MCS | Mbps |
//       +---------+-----+------+
//       | 4'b0000 |  0  |   1  |
//       | 4'b0001 |  1  |   2  |
//       | 4'b0010 |  2  | 5.5  |
//       | 4'b0011 |  3  |  11  |
//       | 4'b1011 |  4  |   6  |
//       | 4'b1111 |  5  |   9  |
//       | 4'b1010 |  6  |  12  |
//       | 4'b1110 |  7  |  18  |
//       | 4'b1001 |  8  |  24  |
//       | 4'b1101 |  9  |  36  |
//       | 4'b1000 | 10  |  48  |
//       | 4'b1100 | 11  |  54  |
//       +---------+-----+------+

always @*
begin
  case (rxLegRate)
      4'b0000 : rxLegRateConv =  4'd0; //   1 Mpbs
      4'b0001 : rxLegRateConv =  4'd1; //   2 Mpbs
      4'b0010 : rxLegRateConv =  4'd2; // 5.5 Mpbs
      4'b0011 : rxLegRateConv =  4'd3; //  11 Mpbs
      4'b1011 : rxLegRateConv =  4'd4; //   6 Mpbs
      4'b1111 : rxLegRateConv =  4'd5; //   9 Mpbs
      4'b1010 : rxLegRateConv =  4'd6; //  12 Mpbs
      4'b1110 : rxLegRateConv =  4'd7; //  18 Mpbs
      4'b1001 : rxLegRateConv =  4'd8; //  24 Mpbs
      4'b1101 : rxLegRateConv =  4'd9; //  36 Mpbs
      4'b1000 : rxLegRateConv = 4'd10; //  48 Mpbs
      4'b1100 : rxLegRateConv = 4'd11; //  54 Mpbs
      // Disable coverage on the default state because it cannot be reached.
      // pragma coverage block = off 
      default : rxLegRateConv =  4'd6; //   6 Mpbs
      // pragma coverage block = on
  endcase
end

assign formatModResp = (txExchangeEnabled) ? formatModTx      : rxFormatMod;

assign mcsPPDU       = (txExchangeEnabled) ? mcsData_comb     : rxMCS;
assign legRatePPDU   = (txExchangeEnabled) ? legRateData_comb : rxLegRateConv;


always @ (posedge macCoreClk or negedge macCoreClkHardRst_n) 
begin
  if (macCoreClkHardRst_n == 1'b0)  // Asynchronous Reset
  begin
    mcsRESP     <= 7'b0; 
    legRateRESP <= 4'b0; 
  end  
  else if (macCoreClkSoftRst_n == 1'b0)  // Synchronous Reset
  begin
    mcsRESP     <= 7'b0; 
    legRateRESP <= 4'b0; 
  end  
  else
    if (started || rateUpdateTxC_p || rateUpdateRxC_p)
    begin
      mcsRESP     <= mcsRESP_comb[6:0]; 
      legRateRESP <= legRateRESP_comb;
    end  
end


// If the control response frame (CTS, ACK or Immediate BlockAck including BlockAck sent as a
// response to an implicit Block Ack request) is carried in a non-HT PPDU, the STA shall select the
// highest rate in the BSSBasicRateSet parameter that is less than or equal to the rate (or non-HT reference
// rate, see 9.6.2) of the previous frame to become the primary rate. If no rate in the BSSBasicRateSet
// parameter meets these conditions, the STA shall select the highest mandatory rate of the
// attached PHY that is less than or equal to the rate (or non-HT reference rate, see 9.6.2) of the previous
// frame to be the primary rate.


// The choice of a response MCS is made as follows:
// a) If the frame eliciting the response is within a non-HT PPDU,
//  1)Eliminate from the CandidateMCSSet all MCSs that have a Data Rate greater than or equal to
//    the Data Rate of the received PPDU (the mapping of MCS to Data Rate is defined in 20.6).
//  2)Find the highest indexed MCS from the CandidateMCSSet. The index of this MCS is the index
//    of the MCS that is the primary MCS for the response transmission.
//  3)If the CandidateMCSSet is empty, the primary MCS is the lowest indexed MCS of the mandatory
//     MCSs.
// b) If the frame eliciting the response is within an HT-PPDU,
//  1)Eliminate from the CandidateMCSSet all MCSs that have an index that is higher than the index
//    of the MCS of the received frame.
//  2)Determine the highest number of spatial streams (NSS) value of the MCSs in the CandidateMCSSet
//    that is less than or equal to the NSS value of the MCS of the received frame. Eliminate all
//    MCSs from the CandidateMCSSet that have an NSS value that is not equal to this NSS value.
//    The mapping from MCS to NSS is dependent on the attached PHY. For the HT PHY, see 20.6.
//  3)Find the highest-indexed MCS of the CandidateMCSSet for which the modulation value of
//    each stream is less than or equal to the modulation value of each stream of the MCS of the
//    received frame and for which the coding rate value is less than or equal to the coding rate value
//    of the MCS from the received frame. The index of this MCS is the index of the MCS that is the
//    primary MCS for the response transmission. The mapping from MCS to modulation and coding
//    rate is dependent on the attached PHY. For the HT PHY, see 20.6. For the purpose of comparing
//    modulation values, the following sequence shows increasing modulation values: BPSK,
//    QPSK, 16-QAM, 64-QAM.
//  4)If there is no MCS that meets the condition in step 3), repeat step 3) beginning with the set of
//    MCS with the NSS value that is one less than the NSS value found in step 2) from the Candi
always @*
begin
  if (formatModResp[2:1] == 2'b0)
  begin
    mcsRespSet  = 16'b0000000000000000;
    case (legRatePPDU)
         4'd0 : legRateRespSet = 13'b0000000000001; // 1
         4'd1 : legRateRespSet = 13'b0000000000011; // 1-2
         4'd2 : legRateRespSet = 13'b0000000000111; // 1-5.5
         4'd3 : legRateRespSet = 13'b0000000001111; // 1-11
         4'd4 : legRateRespSet = 13'b0000000010000; // 6
         4'd5 : legRateRespSet = 13'b0000000110000; // 6-9
         4'd6 : legRateRespSet = 13'b0000001110000; // 6-12
         4'd7 : legRateRespSet = 13'b0000011110000; // 6-18
         4'd8 : legRateRespSet = 13'b0000111110000; // 6-24
         4'd9 : legRateRespSet = 13'b0001111110000; // 6-36
        4'd10 : legRateRespSet = 13'b0011111110000; // 6-48
        4'd11 : legRateRespSet = 13'b0111111110000; // 6-54
      default : legRateRespSet = 13'b0000000010000;
    endcase  
  end
  else if ((formatModResp == 3'd2) || (formatModResp == 3'd3))
  begin
    case (mcsPPDU[6:0])
      7'd0    : 
        begin  // BPSK        1/2
          mcsRespSet  = 16'b0000000000000001; // Only BPSK 1/2 are allowed (MCS : 0)
          legRateRespSet = 13'b0000000010000; // 6Mbps
        end  
      7'd1    :  
        begin  // QPSK        1/2
          mcsRespSet  = 16'b0000000000000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 1-0)
          legRateRespSet = 13'b0000001110000; // 6-12Mbps
        end  
      7'd2    :  
        begin // QPSK        3/4
          mcsRespSet  = 16'b0000000000000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 2-0)
          legRateRespSet = 13'b0000011110000; // 6-18Mbps
        end  
      7'd3    :  
        begin // 16-QAM        1/2
          mcsRespSet  = 16'b0000000000001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 3,1-0)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd4    :  
        begin // 16-QAM        3/4
          mcsRespSet  = 16'b0000000000011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 4-0)
          legRateRespSet = 13'b0001111110000; // 6-36Mbps
        end  
      7'd5    :  
        begin // 64-QAM        2/3
          mcsRespSet  = 16'b0000000000101011; // Only 64QAM 2/3, 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 5,3,1-0)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd6    :  
        begin // 64-QAM        3/4
          mcsRespSet  = 16'b0000000001111111; // Only 64QAM 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 6-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd7    :  
        begin // 64-QAM        5/6
          mcsRespSet  = 16'b0000000011111111; // Only 64QAM 5/6 & 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 7-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `ifdef RW_MAC_2SS_SUPPORT
      7'd8    :  
        begin  // BPSK        1/2
          mcsRespSet  = 16'b0000000100000001; // Only BPSK 1/2 are allowed (MCS : 8,0)
          legRateRespSet = 13'b0000000010000; // 6Mbps
        end  
      7'd9    :  
        begin // QPSK        1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 9-0,1-0)
          legRateRespSet = 13'b0000001110000; // 6-12Mbps
        end  
      7'd10   :  
        begin // QPSK        3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 10-8,2-0)
          legRateRespSet = 13'b0000011110000; // 6-18Mbps
        end  
      7'd11   :  
        begin // 16-QAM        1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 11,9-8,3,1-0)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd12   :  
        begin // 16-QAM        3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 12-8,4-0)
          legRateRespSet = 13'b0001111110000; // 6-36Mbps
        end  
      7'd13   :  
        begin // 64-QAM        2/3
          mcsRespSet  = 16'b0010101100101011;  // Only 64QAM 2/3, 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 13,11,9-8,5,3,1-0)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd14   :  
        begin // 64-QAM        3/4
          mcsRespSet  = 16'b0111111111111111; // Only 64QAM 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 14-8,6-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd15   :  
        begin // 64-QAM        5/6
          mcsRespSet  = 16'b1111111111111111; // Only 64QAM 5/6 & 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 15-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `endif // RW_MAC_2SS_SUPPORT
    `ifdef RW_MAC_3SS_SUPPORT
      7'd16   :  
        begin  // BPSK        1/2
          mcsRespSet  = 16'b0000000100000001; // Only BPSK 1/2 are allowed (MCS : 8,0)
          legRateRespSet = 13'b0000000010000; // 6Mbps
        end  
      7'd17   :  
        begin // QPSK        1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 9-0,1-0)
          legRateRespSet = 13'b0000001110000; // 6-12Mbps
        end  
      7'd18   :  
        begin // QPSK        3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 10-8,2-0)
          legRateRespSet = 13'b0000011110000; // 6-18Mbps
        end  
      7'd19   :  
        begin // 16-QAM        1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 11,9-8,3,1-0)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd20   :  
        begin // 16-QAM        3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 12-8,4-0)
          legRateRespSet = 13'b0001111110000; // 6-36Mbps
        end  
      7'd21   :  
        begin // 64-QAM        2/3
          mcsRespSet  = 16'b0010101100101011;  // Only 64QAM 2/3, 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 13,11,9-8,5,3,1-0)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd22   :  
        begin // 64-QAM        3/4
          mcsRespSet  = 16'b0111111111111111; // Only 64QAM 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 14-8,6-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd23   :  
        begin // 64-QAM        5/6
          mcsRespSet  = 16'b1111111111111111; // Only 64QAM 5/6 & 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 15-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `endif // RW_MAC_3SS_SUPPORT
    `ifdef RW_MAC_4SS_SUPPORT
      7'd24   :  
        begin  // BPSK        1/2
          mcsRespSet  = 16'b0000000100000001; // Only BPSK 1/2 are allowed (MCS : 8,0)
          legRateRespSet = 13'b0000000010000; // 6Mbps
        end  
      7'd25   :  
        begin // QPSK        1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 9-0,1-0)
          legRateRespSet = 13'b0000001110000; // 6-12Mbps
        end  
      7'd26   :  
        begin // QPSK        3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 10-8,2-0)
          legRateRespSet = 13'b0000011110000; // 6-18Mbps
        end  
      7'd27   :  
        begin // 16-QAM        1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 11,9-8,3,1-0)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd28   :  
        begin // 16-QAM        3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 12-8,4-0)
          legRateRespSet = 13'b0001111110000; // 6-36Mbps
        end  
      7'd29   :  
        begin // 64-QAM        2/3
          mcsRespSet  = 16'b0010101100101011;  // Only 64QAM 2/3, 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 13,11,9-8,5,3,1-0)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd30   :  
        begin // 64-QAM        3/4
          mcsRespSet  = 16'b0111111111111111; // Only 64QAM 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 14-8,6-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd31   :  
        begin // 64-QAM        5/6
          mcsRespSet  = 16'b1111111111111111; // Only 64QAM 5/6 & 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 15-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `endif // RW_MAC_4SS_SUPPORT

    `ifdef RW_MAC_2SS_SUPPORT
      // Unequal Mod
      7'd33   :  
        begin // 16-QAM QPSK      1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd34   :  
        begin // 64-QAM QPSK      1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd35   :  
        begin // 64-QAM 16-QAM      1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1,3 8,9,11)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd36   :  
        begin // 16-QAM QPSK      3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0001111110000; // 6-36Mbps
        end  
      7'd37   :  
        begin  // 64-QAM QPSK      3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd38   :  
        begin  // 64-QAM  16-QAM      3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2,3,4 8,9,10,11,12)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `endif // RW_MAC_2SS_SUPPORT
    `ifdef RW_MAC_3SS_SUPPORT
      7'd39   :  
        begin // 16-QAM  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd40   :  
        begin // 16-QAM  16-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd41   :  
        begin // 64-QAM  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd42   :  
        begin // 64-QAM  16-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd43   :  
        begin // 64-QAM  16-QAM  16-QAM    1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1,3 8,9,11)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd44   :  
        begin // 64-QAM 64-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd45   :  
        begin // 64-QAM  64-QAM  16-QAM    1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1,3 8,9,11)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd46   :  
        begin  // 16-QAM  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd47   :  
        begin  // 16-QAM  16-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd48   :  
        begin  // 64-QAM  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd49   :  
        begin  // 64-QAM  16-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd50   :  
        begin  // 64-QAM  16-QAM  16-QAM    3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2,3,4 8,9,10,11,12)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd51   :  
        begin  // 64-QAM  64-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd52   :  
        begin  // 64-QAM  64-QAM  16-QAM    3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2,3,4 8,9,10,11,12)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `endif // RW_MAC_3SS_SUPPORT

    `ifdef RW_MAC_4SS_SUPPORT
      7'd53   :  
        begin // 16-QAM  QPSK  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd54   :  
        begin // 16-QAM  16-QAM  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd55   :  
        begin // 16-QAM  16-QAM  16-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd56   :  
        begin // 64-QAM  QPSK  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd57   :  
        begin // 64-QAM  16-QAM  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd58   :  
        begin // 64-QAM  16-QAM  16-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd59   :  
        begin // 64-QAM  16-QAM  16-QAM  16-QAM    1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1,3 8,9,11)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd60   :  
        begin // 64-QAM 64-QAM  QPSK  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd61   :  
        begin // 64-QAM 64-QAM 16-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd62   :  
        begin // 64-QAM  64-QAM  16-QAM  16-QAM    1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1,3 8,9,11)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd63   :  
        begin // 64-QAM 64-QAM 64-QAM  QPSK    1/2
          mcsRespSet  = 16'b0000001100000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1 8,9)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd64   :  
        begin // 64-QAM  64-QAM  64-QAM  16-QAM    1/2
          mcsRespSet  = 16'b0000101100001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 0,1,3 8,9,11)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd65   :  
        begin  // 16-QAM  QPSK  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd66   :  
        begin  // 16-QAM  16-QAM  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd67   :  
        begin  // 16-QAM  16-QAM  16-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd68   :  
        begin  // 64-QAM  QPSK  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd69   :  
        begin  // 64-QAM  16-QAM  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd70   :  
        begin  // 64-QAM  16-QAM  16-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd71   :  
        begin  // 64-QAM  16-QAM  16-QAM  16-QAM    3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2,3,4 8,9,10,11,12)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd72   :  
        begin  // 64-QAM  64-QAM  QPSK  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd73   :  
        begin  // 64-QAM  64-QAM  16-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd74   :  
        begin  // 64-QAM  64-QAM  16-QAM  16-QAM    3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2,3,4 8,9,10,11,12)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd75   :  
        begin  // 64-QAM  64-QAM  64-QAM  QPSK    3/4
          mcsRespSet  = 16'b0000011100000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2 8,9,10)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd76   :  
        begin  // 64-QAM  64-QAM  64-QAM  16-QAM    3/4
          mcsRespSet  = 16'b0001111100011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2  are allowed (MCS : 0,1,2,3,4 8,9,10,11,12)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
    `endif // RW_MAC_4SS_SUPPORT
    
      // Disable coverage on the default state because it cannot be reached.
      // pragma coverage block = off 
      default :  
        begin
          mcsRespSet  = 16'b0000000000000001; // All modulation are allowed.
          legRateRespSet = 13'b0000000010000;
        end  
      // pragma coverage block = on
    endcase  
  end
  else if (formatModResp == 3'd4)
  begin
    case (mcsPPDU[6:0])
      7'd0    : 
        begin  // BPSK        1/2
          mcsRespSet  = 16'b0000000000000001; // Only BPSK 1/2 are allowed (MCS : 0)
          legRateRespSet = 13'b0000000010000; // 6Mbps
        end  
      7'd1    :  
        begin  // QPSK        1/2
          mcsRespSet  = 16'b0000000000000011; // Only QPSK 1/2 and BPSK 1/2 are allowed (MCS : 1-0)
          legRateRespSet = 13'b0000001110000; // 6-12Mbps
        end  
      7'd2    :  
        begin // QPSK        3/4
          mcsRespSet  = 16'b0000000000000111; // Only QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 2-0)
          legRateRespSet = 13'b0000011110000; // 6-18Mbps
        end  
      7'd3    :  
        begin // 16-QAM        1/2
          mcsRespSet  = 16'b0000000000001011; // Only 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 3,1-0)
          legRateRespSet = 13'b0000111110000; // 6-24Mbps
        end  
      7'd4    :  
        begin // 16-QAM        3/4
          mcsRespSet  = 16'b0000000000011111; // Only 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 4-0)
          legRateRespSet = 13'b0001111110000; // 6-36Mbps
        end  
      7'd5    :  
        begin // 64-QAM        2/3
          mcsRespSet  = 16'b0000000000101011; // Only 64QAM 2/3, 16-QAM 1/2, QPSK 1/2 and BPSK 1/2 are allowed (MCS : 5,3,1-0)
          legRateRespSet = 13'b0011111110000; // 6-48Mbps
        end  
      7'd6    :  
        begin // 64-QAM        3/4
          mcsRespSet  = 16'b0000000001111111; // Only 64QAM 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 6-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd7    :  
        begin // 64-QAM        5/6
          mcsRespSet  = 16'b0000000011111111; // Only 64QAM 5/6 & 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 7-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd8    :  
        begin // 256-QAM        3/4
          mcsRespSet  = 16'b0000000101111111; // Only 256QAM, 64QAM 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 8,6-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      7'd9    :  
        begin // 256-QAM        5/6
          mcsRespSet  = 16'b0000001111111111; // Only 256QAM 5/6 & 3/4, 64QAM 5/6 & 3/4 & 2/3, 16-QAM 1/2 & 3/4, QPSK 1/2 & 3/4 and BPSK 1/2 are allowed (MCS : 9-0)
          legRateRespSet = 13'b0111111110000; // 6-54Mbps
        end  
      // Disable coverage on the default state because it cannot be reached.
      // pragma coverage block = off 
      default :  
        begin
          mcsRespSet  = 16'b0000000000000001; // All modulation are allowed.
          legRateRespSet = 13'b0000000010000;
        end  
      // pragma coverage block = on
    endcase  
  end
  else
  begin
    mcsRespSet  = 16'b0000000000000001; // All modulation are allowed.
    legRateRespSet = 13'b0000000010000;
  end
end


// This combinational process assigns legRateRESP_comb and mcsRESP_comb
//
// 1- In case of Legacy Rate (rxFormatMod = 3'd0 or 3'd1), 
//      legRateRESP_comb takes the highest common value between legRateSet and bssBasicRateSet 
//      (logical AND between legRateSet and bssBasicRateSet)
//      mcsRESP_comb is set to 0
//
// 2- In case of HT Rate (rxFormatMod = 3'd2 or 3'd3), 
//      legRateRESP_comb is set to 4'd4 (6Mbps)
//
//   2.1- If STBC 
//        mcsRESP_comb takes the basicSTBCMCS
//
//   2.2- If MCS received is equal modulation (<32)
//        mcsRESP_comb takes the highest common value between mcsSet and bssBasicHTMCSSetEM 
//        (logical AND between mcsSet and bssBasicHTMCSSetEM)
//
//   2.3- If MCS received is unequal modulation (>32)
//        mcsRESP_comb takes the highest common value between mcsSet and bssBasicHTMCSSetEM 
//        (logical AND between mcsSet and bssBasicHTMCSSetEM)
//
//   2.4- If MCS received is 32
//        mcsRESP_comb is set to 32.
//
// 3- In case of VHT Rate (rxFormatMod = 3'd4), 
//      legRateRESP_comb is set to 4'd4 (6Mbps)
//
//   2.1- If STBC 
//        mcsRESP_comb takes the basicSTBCMCS
//
//   2.2- else
//        mcsRESP_comb takes the highest common value between mcsSet and bssBasicVHTMCSSet.
//        Note : the 256QAM modulation is never selected for response frame 
//

assign legRateRESPCond1 = legRateRespSet[11:0] & bssBasicRateSet;
assign mcsRESPCond1 = mcsRespSet & bssBasicHTMCSSetEM;
assign mcsRESPCond2 = mcsRespSet & mcsRespMandatorySet;
assign mcsRESPCond3 = mcsRespSet[5:0] & bssBasicHTMCSSetEM[5:0];

// The 256QAM is never used for response frame.
assign mcsRESPCond4 = mcsRespSet[9:0] & 10'b0011111111; // MCS 7-0 allowed 

always @*
begin
  
  casex (legRateRESPCond1)
    // Use highest rate in the BSSBasicRateSet <= rate or non-HT reference rate of the previously received frame
    12'b000000000001 : legRateRESP_comb = 4'd0;  //  1   Mbps
    12'b00000000001x : legRateRESP_comb = 4'd1;  //  2   Mbps
    12'b0000000001xx : legRateRESP_comb = 4'd2;  //  5.5 Mbps
    12'b000000001xxx : legRateRESP_comb = 4'd3;  // 11   Mbps
    12'b00000001xxxx : legRateRESP_comb = 4'd4;  //  6   Mbps
    12'b0000001xxxxx : legRateRESP_comb = 4'd5;  //  9   Mbps
    12'b000001xxxxxx : legRateRESP_comb = 4'd6;  // 12   Mbps
    12'b00001xxxxxxx : legRateRESP_comb = 4'd7;  // 18   Mbps
    12'b0001xxxxxxxx : legRateRESP_comb = 4'd8;  // 24   Mbps
    12'b001xxxxxxxxx : legRateRESP_comb = 4'd9;  // 36   Mbps
    12'b01xxxxxxxxxx : legRateRESP_comb = 4'd10; // 48   Mbps
    12'b1xxxxxxxxxxx : legRateRESP_comb = 4'd11; // 54   Mbps
    default          : 
      // If none of the rate defined in bssBasicRateSet matches, Use the highest mandatory rate <= rate 
      // or non-HT reference rate of the previously received frame. 
      // Mandatory rates are 6, 12 and 24 Mbps and 1, 2, 5.5 and 11 Mbps.
      begin
        if (legRateRespSet[11:8] != 4'b0000)  // rate of the response frame bigger or equal to 24Mbps
          legRateRESP_comb = 4'd8;            // Select 24Mbps for the response frame   
        else if (legRateRespSet[7:6] != 2'b00)// rate of the response frame bigger or equal to 12Mbps
          legRateRESP_comb = 4'd6;            // Select 12Mbps for the response frame   
        else if (legRateRespSet[5:4] != 2'b00)// rate of the response frame smaller than 12Mbps 
          legRateRESP_comb = 4'd4;            // Select 6Mbps for the response frame 
        else                                  // rate of the received frame DSSS/CCK
          legRateRESP_comb = legRatePPDU;     // Select the same rate for the response frame
      end 
  endcase  

  // If the frame eliciting the response was an STBC frame and the Dual CTS Protection bit is equal to 1,
  // the CandidateMCSSet shall contain only the basic STBC MCS.
  if ((stbc != 2'b0) && dualCTSProt)
    mcsRESP_comb = basicSTBCMCS;
  else if ((formatModResp == 3'd2) || (formatModResp == 3'd3))
  begin
  `ifdef RW_MAC_2SS_SUPPORT
	  if (mcsPPDU < 7'd32)
	  begin
  `endif // RW_MAC_2SS_SUPPORT
	    casex (mcsRESPCond1)
	      16'b0000000000000001 : mcsRESP_comb = 7'd0;
	      16'b000000000000001x : mcsRESP_comb = 7'd1;
	      16'b00000000000001xx : mcsRESP_comb = 7'd2;
	      16'b0000000000001xxx : mcsRESP_comb = 7'd3;
	      16'b000000000001xxxx : mcsRESP_comb = 7'd4;
	      16'b00000000001xxxxx : mcsRESP_comb = 7'd5;
	      16'b0000000001xxxxxx : mcsRESP_comb = 7'd6;
	      16'b000000001xxxxxxx : mcsRESP_comb = 7'd7;
      `ifdef RW_MAC_2SS_SUPPORT
	      16'b00000001xxxxxxxx : mcsRESP_comb = 7'd8;
	      16'b0000001xxxxxxxxx : mcsRESP_comb = 7'd9;
	      16'b000001xxxxxxxxxx : mcsRESP_comb = 7'd10;
	      16'b00001xxxxxxxxxxx : mcsRESP_comb = 7'd11;
	      16'b0001xxxxxxxxxxxx : mcsRESP_comb = 7'd12;
	      16'b001xxxxxxxxxxxxx : mcsRESP_comb = 7'd13;
	      16'b01xxxxxxxxxxxxxx : mcsRESP_comb = 7'd14;
	      16'b1xxxxxxxxxxxxxxx : mcsRESP_comb = 7'd15;
      `endif // RW_MAC_2SS_SUPPORT
	      default              : 
	      begin
	        // If any step is stuck because the candidateMCSSet = 0, or no MCS in the candidateMCSSet satisfies, 
	        //then set candidateMCSSet = Mandatory HT PHY MCSs, and repeat the above steps.
	        casex (mcsRESPCond2)
	          16'b0000000000000001 : mcsRESP_comb = 7'd0;
	          16'b000000000000001x : mcsRESP_comb = 7'd1;
	          16'b00000000000001xx : mcsRESP_comb = 7'd2;
	          16'b0000000000001xxx : mcsRESP_comb = 7'd3;
	          16'b000000000001xxxx : mcsRESP_comb = 7'd4;
	          16'b00000000001xxxxx : mcsRESP_comb = 7'd5;
	          16'b0000000001xxxxxx : mcsRESP_comb = 7'd6;
	          16'b000000001xxxxxxx : mcsRESP_comb = 7'd7;
	        `ifdef RW_MAC_2SS_SUPPORT
            16'b00000001xxxxxxxx : mcsRESP_comb = 7'd8;
	          16'b0000001xxxxxxxxx : mcsRESP_comb = 7'd9;
	          16'b000001xxxxxxxxxx : mcsRESP_comb = 7'd10;
	          16'b00001xxxxxxxxxxx : mcsRESP_comb = 7'd11;
	          16'b0001xxxxxxxxxxxx : mcsRESP_comb = 7'd12;
	          16'b001xxxxxxxxxxxxx : mcsRESP_comb = 7'd13;
	          16'b01xxxxxxxxxxxxxx : mcsRESP_comb = 7'd14;
	          16'b1xxxxxxxxxxxxxxx : mcsRESP_comb = 7'd15;
	        `endif // RW_MAC_2SS_SUPPORT
            default              : mcsRESP_comb = 7'd0;
	        endcase  
	      end
	      
	    endcase  
  `ifdef RW_MAC_2SS_SUPPORT
	  end
	  else if (mcsPPDU > 7'd32)
	  begin
	    casex (mcsRESPCond3)
	      6'b000001 : mcsRESP_comb = 7'd0;
	      6'b00001x : mcsRESP_comb = 7'd1;
	      6'b0001xx : mcsRESP_comb = 7'd2;
	      6'b001xxx : mcsRESP_comb = 7'd3;
	      6'b01xxxx : mcsRESP_comb = 7'd4;
	      6'b1xxxxx : mcsRESP_comb = 7'd5;
	      default   : mcsRESP_comb = 7'd0;
	    endcase  
	  end
	  else
	    mcsRESP_comb = 7'd32;
  `endif // RW_MAC_2SS_SUPPORT
  end
  else if (formatModResp == 3'd4)
  begin
    casex (mcsRESPCond4)
      10'b0000000001 : mcsRESP_comb = 7'd0;
      10'b000000001x : mcsRESP_comb = 7'd1;
      10'b00000001xx : mcsRESP_comb = 7'd2;
      10'b0000001xxx : mcsRESP_comb = 7'd3;
      10'b000001xxxx : mcsRESP_comb = 7'd4;
      10'b00001xxxxx : mcsRESP_comb = 7'd5;
      10'b0001xxxxxx : mcsRESP_comb = 7'd5; // The MCS6, in VHT is also removed in order to avoid the NSS 3 80MHz case      
      10'b001xxxxxxx : mcsRESP_comb = 7'd7;
       	   default   : mcsRESP_comb = 7'd0;
    endcase
  end
  else    
    mcsRESP_comb = 7'd0;
end

// If our device is AP, then the mandatory rates for the response are 0-7.
// If our device is STA, then the mandatory rates for the response are 0-15.
assign mcsRespMandatorySet = (ap) ? 16'b0000000011111111 :  16'b1111111111111111;

//////////////////////////////////////////////////////////////////////////////
// End of Response Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Begining of Response Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////

assign mcsCFEND = 7'b0;

always @*
begin
  casex (bssBasicRateSet)
    12'b000000000001 : legRateCFEND = 4'd0;
    12'b00000000001x : legRateCFEND = 4'd1;
    12'b0000000001xx : legRateCFEND = 4'd2;
    12'b000000001xxx : legRateCFEND = 4'd3;
    12'b00000001xxxx : legRateCFEND = 4'd4;
    12'b0000001xxxxx : legRateCFEND = 4'd5;
    12'b000001xxxxxx : legRateCFEND = 4'd6;
    12'b00001xxxxxxx : legRateCFEND = 4'd7;
    12'b0001xxxxxxxx : legRateCFEND = 4'd8;
    12'b001xxxxxxxxx : legRateCFEND = 4'd9;
    12'b01xxxxxxxxxx : legRateCFEND = 4'd10;
    12'b1xxxxxxxxxxx : legRateCFEND = 4'd11;
    default          : legRateCFEND = 4'd0;
  endcase  
end

//////////////////////////////////////////////////////////////////////////////
// End of CF-END Frame Rate Selection
//////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Additional Code to ease verification
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

`ifdef RW_SIMU_ON
// Disable coverage on the default state because it cannot be reached.
// pragma coverage block = off 

reg [7*8:0] legRatePPDU_str;
reg [7*8:0] legRateRESP_str;
reg [7*8:0] legRatePROT_str;
reg [7*8:0] legRateCFEND_str;
reg [7*8:0] legRateData_str;
reg [7*8:0] rxLegRate_str;

always @*
begin
  case (legRatePPDU)
         4'd0 :  legRatePPDU_str = {"  1Mbps"};  
         4'd1 :  legRatePPDU_str = {"  2Mbps"};  
         4'd2 :  legRatePPDU_str = {"5.5Mbps"};  
         4'd3 :  legRatePPDU_str = {" 11Mbps"};  
         4'd4 :  legRatePPDU_str = {"  6Mbps"};  
         4'd5 :  legRatePPDU_str = {"  9Mbps"};  
         4'd6 :  legRatePPDU_str = {" 12Mbps"};  
         4'd7 :  legRatePPDU_str = {" 18Mbps"};  
         4'd8 :  legRatePPDU_str = {" 24Mbps"};  
         4'd9 :  legRatePPDU_str = {" 36Mbps"};  
        4'd10 :  legRatePPDU_str = {" 48Mbps"};  
        4'd11 :  legRatePPDU_str = {" 54Mbps"};  
     default  :  legRatePPDU_str = {"XXX    "};
   endcase
end
always @*
begin
  case (legRateRESP)
         4'd0 :  legRateRESP_str = {"  1Mbps"};  
         4'd1 :  legRateRESP_str = {"  2Mbps"};  
         4'd2 :  legRateRESP_str = {"5.5Mbps"};  
         4'd3 :  legRateRESP_str = {" 11Mbps"};  
         4'd4 :  legRateRESP_str = {"  6Mbps"};  
         4'd5 :  legRateRESP_str = {"  9Mbps"};  
         4'd6 :  legRateRESP_str = {" 12Mbps"};  
         4'd7 :  legRateRESP_str = {" 18Mbps"};  
         4'd8 :  legRateRESP_str = {" 24Mbps"};  
         4'd9 :  legRateRESP_str = {" 36Mbps"};  
        4'd10 :  legRateRESP_str = {" 48Mbps"};  
        4'd11 :  legRateRESP_str = {" 54Mbps"};  
     default  :  legRateRESP_str = {"XXX    "};
   endcase
end
always @*
begin
  case (legRateCFEND)
         4'd0 :  legRateCFEND_str = {"  1Mbps"};  
         4'd1 :  legRateCFEND_str = {"  2Mbps"};  
         4'd2 :  legRateCFEND_str = {"5.5Mbps"};  
         4'd3 :  legRateCFEND_str = {" 11Mbps"};  
         4'd4 :  legRateCFEND_str = {"  6Mbps"};  
         4'd5 :  legRateCFEND_str = {"  9Mbps"};  
         4'd6 :  legRateCFEND_str = {" 12Mbps"};  
         4'd7 :  legRateCFEND_str = {" 18Mbps"};  
         4'd8 :  legRateCFEND_str = {" 24Mbps"};  
         4'd9 :  legRateCFEND_str = {" 36Mbps"};  
        4'd10 :  legRateCFEND_str = {" 48Mbps"};  
        4'd11 :  legRateCFEND_str = {" 54Mbps"};  
     default  :  legRateCFEND_str = {"XXX    "};
   endcase
end
always @*
begin
  case (legRatePROT)
         4'd0 :  legRatePROT_str = {"  1Mbps"};  
         4'd1 :  legRatePROT_str = {"  2Mbps"};  
         4'd2 :  legRatePROT_str = {"5.5Mbps"};  
         4'd3 :  legRatePROT_str = {" 11Mbps"};  
         4'd4 :  legRatePROT_str = {"  6Mbps"};  
         4'd5 :  legRatePROT_str = {"  9Mbps"};  
         4'd6 :  legRatePROT_str = {" 12Mbps"};  
         4'd7 :  legRatePROT_str = {" 18Mbps"};  
         4'd8 :  legRatePROT_str = {" 24Mbps"};  
         4'd9 :  legRatePROT_str = {" 36Mbps"};  
        4'd10 :  legRatePROT_str = {" 48Mbps"};  
        4'd11 :  legRatePROT_str = {" 54Mbps"};  
     default  :  legRatePROT_str = {"XXX    "};
   endcase
end
always @*
begin
  case (legRateData)
         4'd0 :  legRateData_str = {"  1Mbps"};  
         4'd1 :  legRateData_str = {"  2Mbps"};  
         4'd2 :  legRateData_str = {"5.5Mbps"};  
         4'd3 :  legRateData_str = {" 11Mbps"};  
         4'd4 :  legRateData_str = {"  6Mbps"};  
         4'd5 :  legRateData_str = {"  9Mbps"};  
         4'd6 :  legRateData_str = {" 12Mbps"};  
         4'd7 :  legRateData_str = {" 18Mbps"};  
         4'd8 :  legRateData_str = {" 24Mbps"};  
         4'd9 :  legRateData_str = {" 36Mbps"};  
        4'd10 :  legRateData_str = {" 48Mbps"};  
        4'd11 :  legRateData_str = {" 54Mbps"};  
     default  :  legRateData_str = {"XXX    "};
   endcase
end
always @*
begin
  case (rxLegRateConv)
         4'd0 :  rxLegRate_str = {"  1Mbps"};  
         4'd1 :  rxLegRate_str = {"  2Mbps"};  
         4'd2 :  rxLegRate_str = {"5.5Mbps"};  
         4'd3 :  rxLegRate_str = {" 11Mbps"};  
         4'd4 :  rxLegRate_str = {"  6Mbps"};  
         4'd5 :  rxLegRate_str = {"  9Mbps"};  
         4'd6 :  rxLegRate_str = {" 12Mbps"};  
         4'd7 :  rxLegRate_str = {" 18Mbps"};  
         4'd8 :  rxLegRate_str = {" 24Mbps"};  
         4'd9 :  rxLegRate_str = {" 36Mbps"};  
        4'd10 :  rxLegRate_str = {" 48Mbps"};  
        4'd11 :  rxLegRate_str = {" 54Mbps"};  
     default  :  rxLegRate_str = {"XXX    "};
   endcase
end
// pragma coverage block = on 
`endif // RW_SIMU_ON


`ifdef RW_ASSERT_ON

// System Verilog Assertions
////////////////////////////

// $rw_sva Checks, in case on non-HT transmission, if the legRate for a response frame is always equal or smaller than the 
//legacy rate of the frame eliciting this response
//This assertion uses the converted value of legRatePPDU and legRateRESP 
//(from MAC-PHY IF convention to MCS Index convention which is linear)
property responseLegRateCheck_prop;
@(posedge macCoreClk)
    (rateUpdateDone_p && (formatModResp <= 1)) |-> legRatePPDU >= legRateRESP;
endproperty
responseLegRateCheck: assert property (responseLegRateCheck_prop); 


// $rw_sva Checks, in case on HT transmission, if the MCS for a response frame is always equal or smaller than the 
//MCS of the frame eliciting this response
sequence responseMCSCheck1_seq;
    ((mcsPPDU >= mcsRESP));
endsequence

// $rw_sva Checks, in case on HT transmission, if the MCS for a response frame is an equal modulation 
//when the frame eliciting this response had an equal modulation too.
sequence responseMCSCheck2_seq;
    ((mcsPPDU <32) && (mcsRESP < 32));
endsequence

// $rw_sva Checks, in case on HT transmission, if the MCS for a response frame is the optional 40 MHz MCS 32
//when the frame eliciting this response was the optional 40 MHz MCS 32 too.
sequence responseMCSCheck3_seq;
    ((mcsPPDU == 32) && (32 == mcsRESP));
endsequence

// $rw_sva Checks, in case on HT transmission, if the MCS for a response frame is an unequal modulation 
//when the frame eliciting this response had an unequal modulation too.
sequence responseMCSCheck4_seq;
    ((mcsPPDU > 32) && (mcsRESP > 32));
endsequence

// $rw_sva Checks if sequences 1 and one of the sequences 2, 3 or 4 are verified.
property responseMCSCheck_prop;
@(posedge macCoreClk)
    (rateUpdateDone_p && (formatModResp == 2 || formatModResp == 3) && (stbc == 0)) |-> responseMCSCheck1_seq and (responseMCSCheck2_seq or responseMCSCheck3_seq or responseMCSCheck4_seq);
endproperty
responseMCSCheck: assert property (responseMCSCheck_prop); 

// $rw_sva Checks, in case of HT transmission with an equal modulation, 
// if the MCS for a response frame is part of the bssBasicHTMCSSetEM or at least part of the mandatory rate.
sequence responseBasicRateCheck1_seq;
    ((mcsPROT < 32) && ((((2**mcsPROT) & bssBasicHTMCSSetEM) == (2**mcsPROT)) || mcsPROT < 8));
endsequence

// $rw_sva Checks, in case of HT transmission with an unequal modulation, 
// if the MCS for a response frame is part of the bssBasicHTMCSSetUM.
sequence responseBasicRateCheck2_seq;
    ((mcsPROT > 32) && ((((2**mcsPROT)>>33) & bssBasicHTMCSSetUM) == ((2**mcsPROT)>>33)));
endsequence

`endif // RW_ASSERT_ON



endmodule
                 
