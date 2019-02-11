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
// Description      : hostIfAhb files list for verilog/rtl compilation
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

// AHB Bus width
`define RW_AHB_ADDR_WIDTH   'd16
`define RW_AHB_DATA_WIDTH   'd32


// Internal Bus width
`define RW_HOST_DATA_WIDTH    32
`define RW_HOST_ADDR_WIDTH    16
`define RW_REG_ADDR_WIDTH     14
`define RW_REG_DATA_WIDTH     32 

// MIB bus width
`define RW_MIB_DATA_WIDTH     32
`define RW_MIB_ADDR_WIDTH      8
