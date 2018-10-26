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
//    This file incorporates all the defines used in design.
//    for configuarability defines can be modified.       
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
// 
// -----------------------------------------------------------------------------
// --
// --
// -----------------------------------------------------------------------------



`timescale 1ns/10ps


// Size of window for searching active MIB in
// pool of all MIBs
`define RW_MIB_WINDOW_SIZE 16
// Depending on the window size appropiate
// RW_MIB_WINDOW_WIDTH needs to be determined.
`define RW_MIB_WINDOW_WIDTH 5

`define ShiftWindowCnt 5
`define RW_MIB_ADDR_WIDTH 8

// Defines Total number of MIB defined


`define RW_MIB_INDEX_WIDTH 10
`define RW_MIB_DATA_WIDTH 32

// Address of last MIB needs to be updated below.
`define ACTIVE_MIB_LAST_ADDR ((2<<`RW_MIB_ADDR_WIDTH)-4)

`define    IncWidth                  17
`define    TotalMIBDefined           60
