//  --========================================================================--
//  This confidential and proprietary software may be used only as
//  authorised by a licensing agreement from ARM Limited
//    (C) COPYRIGHT 2000-2007 ARM Limited
//        ALL RIGHTS RESERVED
//  The entire notice above must be reproduced on all authorised
//  copies and copies may only be made to the extent permitted
//  by a licensing agreement from ARM Limited.
//  
//  ----------------------------------------------------------------------------
//  Version and Release Control Information:
//  
//  File Name          : Ahb2Apb.v,v
//  File Revision      : 1.9
//  
//  Release Information : BP010-AC-39002-r3p0-00rel0
//  
//  ----------------------------------------------------------------------------
//  Purpose            : Converts AHB peripheral transfers to APB transfers
//  --========================================================================--

`timescale 1ns/1ps

module Ahb2Apb 
  (
   // AHB interface
   HCLK,
   HRESETn,
   HADDR,
   HTRANS,
   HWRITE,
   HWDATA,
   HSEL,
   HREADY,

   HRDATA,
   HREADYOUT,
   HRESP,

   // APB interface
   PRDATA0,
   PRDATA1,
   PRDATA2,
   PRDATA3,
   PRDATA4,
   PRDATA5,
   PRDATA6,
   PRDATA7,
   PRDATA8,
   PRDATA9,
   PRDATA10,
   PRDATA11,
   PRDATA12,
   PRDATA13,
   PRDATA14,
   PRDATA15,
   PRDATA_valid,

   PWDATA,
   PENABLE,
   PSELS0,
   PSELS1,
   PSELS2,
   PSELS3,
   PSELS4,
   PSELS5,
   PSELS6,
   PSELS7,
   PSELS8,
   PSELS9,
   PSELS10,
   PSELS11,
   PSELS12,
   PSELS13,
   PSELS14,
   PSELS15,
   PADDR,
   PWRITE,
   
   // Scan test dummy signals; not connected until scan insertion 
   SCANENABLE,   // Scan Test Mode Enbl
   SCANINHCLK,   // Scan Chain Input   
   SCANOUTHCLK   // Scan Chain Output      
   );
    

// Global signals --------------------------------------------------------------
  input         HCLK;        // AHB Clock
  input         HRESETn;     // AHB Reset

// AHB Slave inputs ------------------------------------------------------------
  input  [31:0] HADDR;       // Address bus
  input  [1:0]  HTRANS;      // Transfer type
  input         HWRITE;      // Transfer direction
  input  [31:0] HWDATA;      // Write data bus
  input         HSEL;        // Bridge slave select
  input         HREADY;      // Transfer done input

// APB Master inputs -----------------------------------------------------------
  input  [31:0] PRDATA0;      // Read data bus
  input  [31:0] PRDATA1;      
  input  [31:0] PRDATA2;      
  input  [31:0] PRDATA3;      
  input  [31:0] PRDATA4;      
  input  [31:0] PRDATA5;      
  input  [31:0] PRDATA6;      
  input  [31:0] PRDATA7;      
  input  [31:0] PRDATA8;      
  input  [31:0] PRDATA9;      
  input  [31:0] PRDATA10;      
  input  [31:0] PRDATA11;      
  input  [31:0] PRDATA12;      
  input  [31:0] PRDATA13;      
  input  [31:0] PRDATA14;      
  input  [31:0] PRDATA15;      
  input         PRDATA_valid;

// Scan test dummy signals; not connected until scan insertion -----------------
  input         SCANENABLE;  // Scan Test Mode Enbl
  input         SCANINHCLK;  // Scan Chain Input

// AHB Slave outputs -----------------------------------------------------------
  output [31:0] HRDATA;      // Read data bus
  output        HREADYOUT;   // Transfer done output
  output [1:0]  HRESP;       // Transfer response

// APB Master outputs ----------------------------------------------------------
  output [31:0] PWDATA;      // Write data bus
  output        PENABLE;     // Data valid strobe
  output        PSELS0;      // Peripheral select 0
  output        PSELS1;      // Peripheral select 1
  output        PSELS2;      // Peripheral select 2
  output        PSELS3;      // Peripheral select 3
  output        PSELS4;      // Peripheral select 4
  output        PSELS5;      // Peripheral select 5
  output        PSELS6;      // Peripheral select 6
  output        PSELS7;      // Peripheral select 7
  output        PSELS8;      // Peripheral select 8
  output        PSELS9;      // Peripheral select 9
  output        PSELS10;     // Peripheral select 10
  output        PSELS11;     // Peripheral select 11
  output        PSELS12;     // Peripheral select 12
  output        PSELS13;     // Peripheral select 13
  output        PSELS14;     // Peripheral select 14
  output        PSELS15;     // Peripheral select 15
  output [31:0] PADDR;       // Address bus
  output        PWRITE;      // Transfer direction

// Scan test dummy signals; not connected until scan insertion -----------------
  output        SCANOUTHCLK; // Scan Chain Output

// Block Overview
//
//   The 16-Slot APB Bridge provides an interface between the high-speed AHB 
// domain and the low-power APB domain. The Bridge appears as a slave on AHB, 
// whereas on APB, it is the master. Read and write transfers on the AHB are 
// converted into corresponding transfers on the APB. As the APB is not 
// pipelined, wait states are added during transfers to and from the APB when 
// the AHB is required to wait for the APB protocol.
//
// The AHB to APB Bridge comprises of a state machine, which is used to control
// the generation of the APB and AHB output signals, and the address decoding 
// logic which is used to generate the APB peripheral select lines. 
// All registers used in the system are clocked from the rising edge of the 
// system clock HCLK, and use the asynchronous reset HRESETn. 
//
// Ahb2Apb states:
//  ST_IDLE     is APB bus idle state entered on reset
//  ST_READ     is read setup
//  ST_RENABLE  is read enable
//  ST_WWAIT    is write wait state
//  ST_WRITE    is write setup
//  ST_WENABLE  is write enable
//  ST_WRITEP   is write setup with pending transfer
//  ST_WENABLEP is write enable with pending transfer

//------------------------------------------------------------------------------
// Constant declarations
//------------------------------------------------------------------------------
  `define ST_IDLE 4'b0000
  `define ST_READ 4'b0001
  `define ST_RENABLE 4'b0100
  `define ST_WWAIT 4'b1001
  `define ST_WRITE 4'b1010
  `define ST_WENABLE 4'b1110
  `define ST_WRITEP 4'b1011
  `define ST_WENABLEP 4'b1111

// EASY Peripherals address decoding values:
  `define S0BASE 4'b0000
  `define S1BASE 4'b0001
  `define S2BASE 4'b0010
  `define S3BASE 4'b0011
  `define S4BASE 4'b0100
  `define S5BASE 4'b0101
  `define S6BASE 4'b0110
  `define S7BASE 4'b0111
  `define S8BASE 4'b1000
  `define S9BASE 4'b1001
  `define S10BASE 4'b1010
  `define S11BASE 4'b1011
  `define S12BASE 4'b1100
  `define S13BASE 4'b1101
  `define S14BASE 4'b1110
  `define S15BASE 4'b1111

// HTRANS transfer type signal encoding:
  `define TRN_IDLE 2'b00
  `define TRN_BUSY 2'b01
  `define TRN_NONSEQ 2'b10
  `define TRN_SEQ 2'b11

// HRESP transfer response signal encoding:
  `define RSP_OKAY 2'b00
  `define RSP_ERROR 2'b01
  `define RSP_RETRY 2'b10
  `define RSP_SPLIT 2'b11


//------------------------------------------------------------------------------
// Signal declarations
//------------------------------------------------------------------------------
  
// Input/Output Signals
  wire        HCLK;
  wire        HRESETn;
  wire [31:0] HADDR;
  wire [1:0]  HTRANS;
  wire        HWRITE;
  wire [31:0] HWDATA;
  wire        HSEL;
  wire        HREADY;
  wire        SCANENABLE;
  wire        SCANINHCLK;
  wire [31:0] PRDATA0;
  wire [31:0] PRDATA1;
  wire [31:0] PRDATA2;
  wire [31:0] PRDATA3;
  wire [31:0] PRDATA4;
  wire [31:0] PRDATA5;
  wire [31:0] PRDATA6;
  wire [31:0] PRDATA7;
  wire [31:0] PRDATA8;
  wire [31:0] PRDATA9;
  wire [31:0] PRDATA10;
  wire [31:0] PRDATA11;
  wire [31:0] PRDATA12;
  wire [31:0] PRDATA13;
  wire [31:0] PRDATA14;
  wire [31:0] PRDATA15;  
  reg  [31:0] HRDATA;
  wire        HREADYOUT;
  wire [1:0]  HRESP;
  wire        SCANOUTHCLK;
  wire        PSELS0;
  wire        PSELS1;
  wire        PSELS2;
  wire        PSELS3;
  wire        PSELS4;
  wire        PSELS5;
  wire        PSELS6;
  wire        PSELS7;
  wire        PSELS8;
  wire        PSELS9;
  wire        PSELS10;
  wire        PSELS11;
  wire        PSELS12;
  wire        PSELS13;
  wire        PSELS14;
  wire        PSELS15;
  
  reg  [31:0] PADDR;
  reg  [31:0] PWDATA;         // Registered APB outputs
  reg         PENABLE;
  reg         PWRITE;

// Internal Signals
  
  wire        Valid;          // Module is selected with valid transfer 
  wire        ACRegEn;        // Enable for address and control registers 
  reg  [31:0] HaddrReg;       // HADDR register 
  reg         HwriteReg;      // HWRITE register 
  wire [31:0] HaddrMux;       // HADDR multiplexer 
  wire [3:0]  HaddrMux15to12; // Slot decoding slice of HaddrMux

  reg  [3:0]  NextState;      // State machine 
  reg  [3:0]  CurrentState;

  wire        HreadyNext;     // HREADYOUT register input 
  reg         HreadyNext_d0;
  reg         iHREADYOUT;     // HREADYOUT register 

  reg         PselS0Int;      // Internal PSELS0 
  reg         PselS1Int;      // Internal PSELS1 
  reg         PselS2Int;      // Internal PSELS2 
  reg         PselS3Int;      // Internal PSELS3 
  reg         PselS4Int;      // Internal PSELS4 
  reg         PselS5Int;      // Internal PSELS5 
  reg         PselS6Int;      // Internal PSELS6 
  reg         PselS7Int;      // Internal PSELS7 
  reg         PselS8Int;      // Internal PSELS8 
  reg         PselS9Int;      // Internal PSELS9 
  reg         PselS10Int;     // Internal PSELS10 
  reg         PselS11Int;     // Internal PSELS11 
  reg         PselS12Int;     // Internal PSELS12 
  reg         PselS13Int;     // Internal PSELS13 
  reg         PselS14Int;     // Internal PSELS14 
  reg         PselS15Int;     // Internal PSELS15 

  wire        APBEn;          // Enable for APB output registers 

  wire        PWDATAEn;       // PWDATA Register enable 
  wire        PenableNext;    // PENABLE register input 

  reg         PselS0Mux;      // PSEL multiplexer values 
  reg         PselS1Mux;
  reg         PselS2Mux;
  reg         PselS3Mux;
  reg         PselS4Mux;
  reg         PselS5Mux;
  reg         PselS6Mux;
  reg         PselS7Mux;
  reg         PselS8Mux;
  reg         PselS9Mux;
  reg         PselS10Mux;
  reg         PselS11Mux;
  reg         PselS12Mux;
  reg         PselS13Mux;
  reg         PselS14Mux;
  reg         PselS15Mux;

  reg         iPSELS0;        //  Internal PSEL outputs 
  reg         iPSELS1;
  reg         iPSELS2;
  reg         iPSELS3;
  reg         iPSELS4;
  reg         iPSELS5;
  reg         iPSELS6;
  reg         iPSELS7;
  reg         iPSELS8;
  reg         iPSELS9;
  reg         iPSELS10;
  reg         iPSELS11;
  reg         iPSELS12;
  reg         iPSELS13;
  reg         iPSELS14;
  reg         iPSELS15;

  reg         PwriteNext;     //  PWRITE register input 


//------------------------------------------------------------------------------
// Beginning of main code
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// Valid transfer detection
//------------------------------------------------------------------------------
// Valid AHB transfers only take place when a non-sequential or sequential
//  transfer is shown on HTRANS - an idle or busy transfer should be ignored.

  assign Valid = ((HSEL == 1'b1 && HREADY == 1'b1 && 
                  (HTRANS == `TRN_NONSEQ || HTRANS == `TRN_SEQ)) ? 1'b1 :
                 1'b0);

//------------------------------------------------------------------------------
// Address and control registers
//------------------------------------------------------------------------------
// Registers are used to store the address and control signals from the address
//  phase for use in the data phase of the transfer.
// Only enabled when the HREADY input is HIGH and the module is addressed.

  assign ACRegEn = HSEL & HREADY;

  always @ (negedge HRESETn or posedge HCLK)
    begin : p_ACRegSeq
      if ((!HRESETn))
        begin 
          HaddrReg <= {32{1'b0}};
          HwriteReg <= 1'b0;
        end
      else
        begin
          if (ACRegEn)
            begin 
              HaddrReg <= HADDR;
              HwriteReg <= HWRITE;
            end 
        end 
    end 

// The address source used depends on the source of the current APB transfer. If
//  the transfer is being generated from:
// - the pipeline registers, then the address source is HaddrReg
// - the AHB inputs, the the address source is HADDR.
//
// The HaddrMux multiplexer is used to select the appropriate address source. A
//  new read, sequential read following another read, or a read following a
//  write with no pending transfer are the only transfers that are generated
//  directly from the AHB inputs. All other transfers are generated from the
//  pipeline registers.
  
  assign HaddrMux = ((NextState == `ST_READ &&
                      (CurrentState == `ST_IDLE || 
                       CurrentState == `ST_RENABLE || 
                       CurrentState == `ST_WENABLE)) ? HADDR :
                    HaddrReg);

//------------------------------------------------------------------------------
// Next state logic for APB state machine
//------------------------------------------------------------------------------
// Generates next state from CurrentState and AHB inputs.
// Due to write transfers having an extra setup state, the pending states are
//  used to indicate that there is a transfer in the pipeline that has not been
//  started on the APB.
// Read transfers start immediately, so pending states are not needed.

  always @ (CurrentState or HWRITE or HwriteReg or Valid)
    begin : p_NextStateComb

      case (CurrentState)
        `ST_IDLE :                 // Idle state
          if (Valid)
            if (HWRITE)
              NextState = `ST_WWAIT;
            else
              NextState = `ST_READ;
          else
            NextState = `ST_IDLE;
   
        `ST_READ :                 // Read setup
          NextState = `ST_RENABLE;

        `ST_WWAIT :                // Hold for one cycle before write
          if (Valid)
            NextState = `ST_WRITEP;
          else
            NextState = `ST_WRITE;
   
        `ST_WRITE :                // Write setup
          if (Valid)
            NextState = `ST_WENABLEP;
          else
            NextState = `ST_WENABLE;
   
        `ST_WRITEP :               // Write setup with pending transfer
          NextState = `ST_WENABLEP;

        `ST_RENABLE :              // Read enable
          if (Valid)
            if (HWRITE)
              NextState = `ST_WWAIT;
            else
              NextState = `ST_READ;
          else
            NextState = `ST_IDLE;
   
        `ST_WENABLE :              // Write enable
          if (Valid)
            if (HWRITE)
              NextState = `ST_WWAIT;
            else
              NextState = `ST_READ;
          else
            NextState = `ST_IDLE;
   
        `ST_WENABLEP :             // Write enable with pending transfer
          if (HwriteReg)
            if (Valid)
              NextState = `ST_WRITEP;
            else
              NextState = `ST_WRITE;
          else
            NextState = `ST_READ;
   
        default  :
          NextState = `ST_IDLE;    // Return to idle on FSM error

      endcase
    end 

//------------------------------------------------------------------------------
// State machine
//------------------------------------------------------------------------------
// Changes state on rising edge of HCLK.
  always @ (negedge HRESETn or posedge HCLK)
    begin : p_CurrentStateSeq
      if ((!HRESETn))
        CurrentState <= `ST_IDLE;
      else
        CurrentState <= NextState;
    end 

//------------------------------------------------------------------------------
// HREADYOUT generation
//------------------------------------------------------------------------------

always @ (posedge HCLK) begin
    HreadyNext_d0 <= HreadyNext;
end 

assign HreadyNext = (CurrentState == `ST_READ || CurrentState == `ST_RENABLE) ? 1'b0 : 1'b1;

assign HREADYOUT = HreadyNext && HreadyNext_d0;


//------------------------------------------------------------------------------
// APB address decoding for slave devices
//------------------------------------------------------------------------------
// Decodes the address from HaddrMux, which only changes during a read or write
//  cycle.
// When an address is used that is not in any of the ranges specified,
//  operation of the system continues, but no PSEL lines are set, so no
//  peripherals are selected during the read/write transfer.
// Operation of PWDATA, PWRITE, PENABLE and PADDR continues as normal.

  assign HaddrMux15to12 = HaddrMux[15:12];

  always @ (HaddrMux15to12)
    begin : p_AddressDecodeComb
      // Default values
      PselS0Int = 1'b0;
      PselS1Int = 1'b0;
      PselS2Int = 1'b0;
      PselS3Int = 1'b0;
      PselS4Int = 1'b0;
      PselS5Int = 1'b0;
      PselS6Int = 1'b0;
      PselS7Int = 1'b0;
      PselS8Int = 1'b0;
      PselS9Int = 1'b0;
      PselS10Int = 1'b0;
      PselS11Int = 1'b0;
      PselS12Int = 1'b0;
      PselS13Int = 1'b0;
      PselS14Int = 1'b0;
      PselS15Int = 1'b0;

      case (HaddrMux15to12)
        `S0BASE : 
          PselS0Int = 1'b1;

        `S1BASE :
           PselS1Int = 1'b1;    

        `S2BASE : 
          PselS2Int = 1'b1;

        `S3BASE : 
          PselS3Int = 1'b1;

        `S4BASE : 
          PselS4Int = 1'b1;

        `S5BASE : 
          PselS5Int = 1'b1;

        `S6BASE : 
          PselS6Int = 1'b1;

        `S7BASE : 
          PselS7Int = 1'b1;

        `S8BASE : 
          PselS8Int = 1'b1;

        `S9BASE : 
          PselS9Int = 1'b1;

        `S10BASE : 
          PselS10Int = 1'b1;

        `S11BASE : 
          PselS11Int = 1'b1;

        `S12BASE : 
          PselS12Int = 1'b1;

        `S13BASE : 
          PselS13Int = 1'b1;

        `S14BASE : 
          PselS14Int = 1'b1;

        `S15BASE : 
          PselS15Int = 1'b1;
       
      endcase
    end 

//------------------------------------------------------------------------------
// APB enable generation
//------------------------------------------------------------------------------
// APBEn is set when starting an access on the APB, and is used to enable the
//  PSEL, PWRITE and PADDR APB output registers.
  
  assign APBEn = ((NextState == `ST_READ || NextState == `ST_WRITE || 
                   NextState == `ST_WRITEP) ? 1'b1 : 
                 1'b0);

//------------------------------------------------------------------------------
// Registered HWDATA for writes (PWDATA)
//------------------------------------------------------------------------------
// Write wait state allows a register to be used to hold PWDATA.
// Register enabled when PWRITE output is set HIGH.

  assign PWDATAEn = PwriteNext;

  always @ (negedge HRESETn or posedge HCLK)
    begin : p_PWDATASeq
      if ((!HRESETn))
        PWDATA <= {32{1'b0}};
      else
        begin
          if (PWDATAEn)
            PWDATA <= HWDATA;
        end
    end 

//------------------------------------------------------------------------------
// PENABLE generation
//------------------------------------------------------------------------------
// PENABLE output is set HIGH during any of the three ENABLE states.

  assign PenableNext = ((NextState == `ST_RENABLE || 
                         NextState == `ST_WENABLE || 
                         NextState == `ST_WENABLEP) ? 1'b1 :
                       1'b0);

  always @ (negedge HRESETn or posedge HCLK)
    begin : p_PENABLESeq
      if ((!HRESETn))
        PENABLE <= 1'b0;
      else
        PENABLE <= PenableNext;
    end 

//------------------------------------------------------------------------------
// iPSEL generation
//------------------------------------------------------------------------------
// Set   outputs with internal values when in READ or WRITE states (APBEn HIGH).
// Reset outputs when APB transfer has ended.
// Hold  outputs at all other times.

  always @ (APBEn or NextState or PselS0Int or PselS1Int or PselS2Int or 
            PselS3Int or PselS4Int or PselS5Int or PselS6Int or 
            PselS7Int or PselS8Int or PselS9Int or PselS10Int or 
            PselS11Int or PselS12Int or PselS13Int or PselS14Int or 
            PselS15Int or iPSELS0 or iPSELS1 or iPSELS2 or iPSELS3 or 
            iPSELS4 or iPSELS5 or iPSELS6 or iPSELS7 or iPSELS8 or 
            iPSELS9 or iPSELS10 or iPSELS11 or iPSELS12 or iPSELS13 or 
            iPSELS14 or iPSELS15)
    begin : p_PselMuxComb
      if (APBEn)
        begin 
          PselS0Mux  = PselS0Int;
          PselS1Mux  = PselS1Int;
          PselS2Mux  = PselS2Int;
          PselS3Mux  = PselS3Int;
          PselS4Mux  = PselS4Int;
          PselS5Mux  = PselS5Int;
          PselS6Mux  = PselS6Int;
          PselS7Mux  = PselS7Int;
          PselS8Mux  = PselS8Int;
          PselS9Mux  = PselS9Int;
          PselS10Mux = PselS10Int;
          PselS11Mux = PselS11Int;
          PselS12Mux = PselS12Int;
          PselS13Mux = PselS13Int;
          PselS14Mux = PselS14Int;
          PselS15Mux = PselS15Int;
        end
          else if ((NextState == `ST_IDLE || NextState == `ST_WWAIT))
            begin 
              PselS0Mux  = 1'b0;
              PselS1Mux  = 1'b0;
              PselS2Mux  = 1'b0;
              PselS3Mux  = 1'b0;
              PselS4Mux  = 1'b0;
              PselS5Mux  = 1'b0;
              PselS6Mux  = 1'b0;
              PselS7Mux  = 1'b0;
              PselS8Mux  = 1'b0;
              PselS9Mux  = 1'b0;
              PselS10Mux = 1'b0;
              PselS11Mux = 1'b0;
              PselS12Mux = 1'b0;
              PselS13Mux = 1'b0;
              PselS14Mux = 1'b0;
              PselS15Mux = 1'b0;
            end
          else
            begin
              PselS0Mux  = iPSELS0;
              PselS1Mux  = iPSELS1;
              PselS2Mux  = iPSELS2;
              PselS3Mux  = iPSELS3;
              PselS4Mux  = iPSELS4;
              PselS5Mux  = iPSELS5;
              PselS6Mux  = iPSELS6;
              PselS7Mux  = iPSELS7;
              PselS8Mux  = iPSELS8;
              PselS9Mux  = iPSELS9;
              PselS10Mux = iPSELS10;
              PselS11Mux = iPSELS11;
              PselS12Mux = iPSELS12;
              PselS13Mux = iPSELS13;
              PselS14Mux = iPSELS14;
              PselS15Mux = iPSELS15;
            end 
    end 
 
// Drives PSEL outputs with internal multiplexer versions.

  always @ (negedge HRESETn or posedge HCLK)
    begin : p_PSELSeq
      if ((!HRESETn))
        begin 
          iPSELS0  <= 1'b0;
          iPSELS1  <= 1'b0;
          iPSELS2  <= 1'b0;
          iPSELS3  <= 1'b0;
          iPSELS4  <= 1'b0;
          iPSELS5  <= 1'b0;
          iPSELS6  <= 1'b0;
          iPSELS7  <= 1'b0;
          iPSELS8  <= 1'b0;
          iPSELS9  <= 1'b0;
          iPSELS10 <= 1'b0;
          iPSELS11 <= 1'b0;
          iPSELS12 <= 1'b0;
          iPSELS13 <= 1'b0;
          iPSELS14 <= 1'b0;
          iPSELS15 <= 1'b0;
        end
      else
        begin
          iPSELS0  <= PselS0Mux;
          iPSELS1  <= PselS1Mux;
          iPSELS2  <= PselS2Mux;
          iPSELS3  <= PselS3Mux;
          iPSELS4  <= PselS4Mux;
          iPSELS5  <= PselS5Mux;
          iPSELS6  <= PselS6Mux;
          iPSELS7  <= PselS7Mux;
          iPSELS8  <= PselS8Mux;
          iPSELS9  <= PselS9Mux;
          iPSELS10 <= PselS10Mux;
          iPSELS11 <= PselS11Mux;
          iPSELS12 <= PselS12Mux;
          iPSELS13 <= PselS13Mux;
          iPSELS14 <= PselS14Mux;
          iPSELS15 <= PselS15Mux;
        end 
    end 

//------------------------------------------------------------------------------
// Registered HADDR for reads and writes (iPADDR)
//------------------------------------------------------------------------------
// HaddrMux is used, as the generation time of the APB address is different for
//  reads and writes, so both the direct and registered HADDR input need to be
//  used.
// HaddrMux is captured by an APBEn enabled register to generate iPADDR.
// PADDR driven on State Machine change to READ or WRITE, with reset to zero.

  always @ (negedge HRESETn or posedge HCLK)
    begin : p_iPADDRSeq
      if ((!HRESETn))
        PADDR <= {32{1'b0}};
      else
        begin
          if (APBEn)
            PADDR <= HaddrMux;
        end 
    end 

//------------------------------------------------------------------------------
// PWRITE generation
//------------------------------------------------------------------------------
// PwriteNext is active when NextState is either ST_WRITE or ST_WRITEP. To avoid
//  a critical path through the main state machine this signal is generated 
//  using CurrentState.
// PwriteNext is captured by an APBEn enabled register to generate PWRITE, and
//  is generated from NextState (set HIGH during a write cycle).
// PWRITE output only changes when APB is accessed.

  always @ (CurrentState or HwriteReg)
    begin : p_PwriteNextComb
      case (CurrentState)
        `ST_WWAIT :
          PwriteNext = 1'b1;

        `ST_WENABLEP : begin
          if (HwriteReg)
            PwriteNext = 1'b1;
          else
            PwriteNext = 1'b0;
        end

        default: 
          PwriteNext = 1'b0;
      endcase
    end 

  always @ (negedge HRESETn or posedge HCLK)
    begin : p_PWRITESeq
      if ((!HRESETn))
        PWRITE <= 1'b0;
      else
        begin
          if (APBEn)
            PWRITE <= PwriteNext;
        end 
    end 

//------------------------------------------------------------------------------
// APB output drivers
//------------------------------------------------------------------------------
// Drive outputs with internal signals.

  assign PSELS0  = iPSELS0;
  assign PSELS1  = iPSELS1;
  assign PSELS2  = iPSELS2;
  assign PSELS3  = iPSELS3;
  assign PSELS4  = iPSELS4;
  assign PSELS5  = iPSELS5;
  assign PSELS6  = iPSELS6;
  assign PSELS7  = iPSELS7;
  assign PSELS8  = iPSELS8;
  assign PSELS9  = iPSELS9;
  assign PSELS10 = iPSELS10;
  assign PSELS11 = iPSELS11;
  assign PSELS12 = iPSELS12;
  assign PSELS13 = iPSELS13;
  assign PSELS14 = iPSELS14;
  assign PSELS15 = iPSELS15;

//------------------------------------------------------------------------------
// AHB output drivers
//------------------------------------------------------------------------------
// PRDATA is only ever driven during a read, so it can be directly copied to
//  HRDATA to reduce the output data delay onto the AHB.

  //assign HRDATA = PRDATA;


  always @ (posedge HCLK)
    begin : p_RdataDecodeComb
      // Default values
      HRDATA = 32'h00000000;
      case (HaddrMux15to12)
        `S0BASE : 
          HRDATA = PRDATA0;

        `S1BASE :
          HRDATA = PRDATA1;    

        `S2BASE : 
          HRDATA = PRDATA2;

        `S3BASE : 
          HRDATA = PRDATA3;

        `S4BASE : 
          HRDATA = PRDATA4;

        `S5BASE : 
          HRDATA = PRDATA5;

        `S6BASE : 
          HRDATA = PRDATA6;

        `S7BASE : 
          HRDATA = PRDATA7;

        `S8BASE : 
          HRDATA = PRDATA8;

        `S9BASE : 
          HRDATA = PRDATA9;

        `S10BASE : 
          HRDATA = PRDATA10;

        `S11BASE : 
          HRDATA = PRDATA11;

        `S12BASE : 
          HRDATA = PRDATA12;

        `S13BASE : 
          HRDATA = PRDATA13;

        `S14BASE : 
          HRDATA = PRDATA14;

        `S15BASE : 
          HRDATA = PRDATA15;
       
      endcase
    end 


// Drives the output port with the internal version, and sets it LOW at all
//  other times when the module is not selected.




// The response will always be OKAY to show that the transfer has been performed
//  successfully.

  assign HRESP = `RSP_OKAY;


endmodule

// --================================= End ===================================--

