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
// Description      : Top level of baController module
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
`default_nettype none

module baController( 
            ///////////////////////////////////////////////
            //$port_g Clock and reset
            ///////////////////////////////////////////////
            input wire         macCoreClk,              // MAC Core Clock
            input wire         macCoreClkHardRst_n,     // Hard Reset of the MAC Core Clock domain active low
            input wire         macCoreClkSoftRst_n,     // Soft Reset of the MAC Core Clock domain
            
            ///////////////////////////////////////////////
            //$port_g TX Controller
            ///////////////////////////////////////////////
            input wire         psBitmapReady,           // PS Bitmap field request

            output wire [ 7:0] psBitmap,                // PS Bitmap field
            output wire        psBitmapValid,           // PS Bitmap field valid
            
            ///////////////////////////////////////////////
            //$port_g RX Controller
            ///////////////////////////////////////////////
            input wire         psBitmapUpdate_p,        // Update Bitmap request
            input wire         psBitmapDiscard_p,       // Discard Bitmap update request
            input wire         rxQoSEnd_p,              // Rx QoS field end pulse
            input wire         barRcved_p,              // When Bar SeqCntrl end pulse

            input wire         baEnable,                // Enable BA Controller procedure
            
            input wire         barRcved,                // BA Request received
            
            input wire  [ 3:0] rxTID,                   // TID
            input wire  [11:0] rxSN,                    // Sequence Number
            input wire  [11:0] rxBASSN,                 // BA Starting Sequence Number
            
            ///////////////////////////////////////////////
            //$port_g Key search Engine
            ///////////////////////////////////////////////
            input wire  [7:0]  keyIndexReturnBA,        // Returned Key Index
            input wire         keyStorageValid_p,       // Returned Key Index valid
            input wire         keyStorageError_p,       // Error indicating key not found
            
            ///////////////////////////////////////////////
            //$port_g Control and Status Register
            ///////////////////////////////////////////////
            input wire         baPSBitmapReset,         // Partial state bitmap Reset
            
            output wire        baPSBitmapResetIn,       // baPSBitmapResetIn
            output wire        baPSBitmapResetInValid,  // Clear the baPSBitmapReset bit
            
            ///////////////////////////////////////////////
            //$port_g PS BITMAP RAM 8*32 Single Port SRAM
            ///////////////////////////////////////////////
            input  wire [87:0] psBitmapReadData,        // Partial State Bitmap Read Data bus.
            
            output wire        psBitmapEn,              // Partial State Bitmap Enable. 
                                                        // This signal is asserted for both read and write operations to the Partial State Bitmap.
            output wire        psBitmapWriteEn,         // Partial State Bitmap Write Enable.
                                                        // This signal is asserted for write operations to the Partial State Bitmap.
            output wire [ 1:0] psBitmapAddr,            // Partial State Bitmap Address bus.
            output wire [87:0] psBitmapWriteData,       // Partial State Bitmap Write Data bus.

            ///////////////////////////////////////////////
            //$port_g Debug port
            ///////////////////////////////////////////////
            output wire [15:0] debugPortBAController,   // Debug port for validation
            output wire [15:0] debugPortBAController2,  // Debug port for validation
            output wire [15:0] debugPortBAController3   // Debug port for validation
            );


//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////
wire        psBitmapUpdateDone_p;    // PS Bitmap update done
wire [63:0] updatedPSBitmap;         // Partial State Bitmap from RAM
wire [11:0] updatedSSN;              // SSN from RAM

wire        startUpdate_p;           // Start PS Bitmap update
wire [63:0] readPSBitmap;            // Partial State Bitmap read from RAM
wire [11:0] readSSN;                 // SSN read from RAM
wire        newPsBitmap;             // Flag to detect new bitmap for the current frame

wire [11:0] rxSNCapt;                // psbitmap current rxSN
wire [11:0] rxBASSNCapt;             // bar current SN

//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////

// Instanciation of baControllerFsm
// Name of the instance : U_baControllerFsm
// Name of the file containing this module : baControllerFsm.v
baControllerFsm U_baControllerFsm (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.psBitmapReady                    (psBitmapReady),
		.psBitmap                         (psBitmap),
		.psBitmapValid                    (psBitmapValid),
		.psBitmapUpdate_p                 (psBitmapUpdate_p),
		.psBitmapDiscard_p                (psBitmapDiscard_p),
		.rxQoSEnd_p                       (rxQoSEnd_p),
    .barRcved_p                       (barRcved_p),
		.baEnable                         (baEnable),
		.rxTID                            (rxTID),
    .rxSN                             (rxSN),
    .rxBASSN                          (rxBASSN),
		.keyIndexReturnBA                 (keyIndexReturnBA),
		.keyStorageValid_p                (keyStorageValid_p),
		.keyStorageError_p                (keyStorageError_p),
		.baPSBitmapReset                  (baPSBitmapReset),
		.baPSBitmapResetIn                (baPSBitmapResetIn),
		.baPSBitmapResetInValid           (baPSBitmapResetInValid),
		.psBitmapReadData                 (psBitmapReadData),
		.psBitmapEn                       (psBitmapEn),
		.psBitmapWriteEn                  (psBitmapWriteEn),
		.psBitmapAddr                     (psBitmapAddr),
		.psBitmapWriteData                (psBitmapWriteData),
		.psBitmapUpdateDone_p             (psBitmapUpdateDone_p),
		.updatedPSBitmap                  (updatedPSBitmap),
		.updatedSSN                       (updatedSSN),
		.startUpdate_p                    (startUpdate_p),
		.readPSBitmap                     (readPSBitmap),
		.readSSN                          (readSSN),
    .newPsBitmap                      (newPsBitmap),
    .rxSNCapt                         (rxSNCapt),
    .rxBASSNCapt                      (rxBASSNCapt),
		.debugPortBAController            (debugPortBAController),
		.debugPortBAController3           (debugPortBAController3)
		);


// Instanciation of scoreboardController
// Name of the instance : U_scoreboardController
// Name of the file containing this module : scoreboardController.v
scoreboardController U_scoreboardController (
		.macCoreClk                       (macCoreClk),
		.macCoreClkHardRst_n              (macCoreClkHardRst_n),
		.macCoreClkSoftRst_n              (macCoreClkSoftRst_n),
		.barRcved                         (barRcved),
		.rxSN                             (rxSNCapt),
		.rxBASSN                          (rxBASSNCapt),
		.startUpdate_p                    (startUpdate_p),
		.readPSBitmap                     (readPSBitmap),
		.readSSN                          (readSSN),
    .newPsBitmap                      (newPsBitmap),
    .baPSBitmapReset                  (baPSBitmapReset),
		.psBitmapUpdateDone_p             (psBitmapUpdateDone_p),
		.updatedPSBitmap                  (updatedPSBitmap),
		.updatedSSN                       (updatedSSN),
    .debugPortBAController2           (debugPortBAController2)
		);



endmodule
                 
