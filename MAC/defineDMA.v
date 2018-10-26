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
// Description      : Defines for the RTL
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
 
//Enable assertions define
//`define RW_ASSERT_ON      

//RX List Processor defines
`define SIZE_RX_HDR_DESC       'd17 //in quadlets
`define RHD_SIZE               17
`define SIZE_RX_PLD_DESC       'd5 //in quadlets
`define RBD_SIZE               5



//RX HDR DESCRIPTOR defines
//Gives the location of the field
//in the header descriptor
`define RX_DMA_PATTERN         'd01
`define RX_NXT_HDR_DESC_PTR    'd02
`define RX_FIRST_PLD_DESC_PTR  'd03
`define RX_HDR_BUF_START_PTR   'd05
`define RX_HDR_BUF_END_PTR     'd06
`define RX_HDR_CTRL_INFO       'd07
`define RX_HDR_STATUS_INFO     'd17

//RX PLD DESCRIPTOR defines
`define RX_NXT_PLD_DESC_PTR    'd02
`define RX_PLD_BUF_START_PTR   'd03
`define RX_PLD_BUF_END_PTR     'd04
`define RX_PLD_STATUS_INFO     'd05

//TX List Processor defines
`ifdef RW_THD_V2
  `define SIZE_TX_HDR_DESC       'd15 //in quadlets
  `define THD_SIZE                15
`else // RW_THD_V2
  `define SIZE_TX_HDR_DESC      'd17 //in quadlets
  `define THD_SIZE                17
`endif // RW_THD_V2
`define SIZE_TX_PLD_DESC       'd5  //in quadlets
`define TBD_SIZE                 4
`define SIZE_TX_PLY_TBL       'd13 //in quadlets
`define PT_SIZE                 13
 
//UNIQUE PATTERN POSSTION
`define TX_UNIQUE_PATTERN      'd01

//TX HDR DESCRIPTOR defines
`define TX_DMA_PATTERN         'd01
`define TX_NXT_ATOM_FRM_PTR    'd02
`define TX_NXT_MPDU_DESC_PTR   'd03
`define TX_FIRST_PLD_DESC_PTR  'd04
`define TX_HDR_BUF_START_PTR   'd05
`define TX_HDR_BUF_END_PTR     'd06
`define TX_LENGTH_INFO         'd07
`define TX_FRAME_LIFETIME      'd08
`define TX_PHY_CTRL_INFO       'd09
`define TX_PLY_ENTRY_ADDR      'd10
`ifdef RW_THD_V2
  `define TX_MAC_CTRL1_INFO      'd13
  `define TX_MAC_CTRL2_INFO      'd14
  `define TX_STATUS_INFO         'd15
`else // RW_THD_V2
  `define TX_LENGTH_INFO_DROP20  'd11
  `define TX_LENGTH_INFO_DROP40  'd12
  `define TX_LENGTH_INFO_DROP80  'd13
  `define TX_MAC_CTRL1_INFO      'd14
  `define TX_MAC_CTRL2_INFO      'd15
  `define TX_STATUS_INFO         'd16
  `define TX_MEDIUM_TIME_USED    'd17
`endif // RW_THD_V2

//TX PLD DESCRIPTOR defines
`define TX_PLD_BUF_DMA_PATTERN 'd01
`define TX_NXT_PLD_DESC_PTR    'd02
`define TX_PLD_BUF_START_PTR   'd03
`define TX_PLD_BUF_END_PTR     'd04
`define TX_PLD_BUF_STATUS      'd05

//POLICY TABLE defines
`define PLY_TBL_DMA_PATTERN     'd01
`define PLY_TBL_PHY_CTRL_INFO1  'd02
`define PLY_TBL_PHY_CTRL_INFO2  'd03
`define PLY_TBL_MAC_CTRL_INFO1  'd04
`define PLY_TBL_MAC_CTRL_INFO2  'd05
`define PLY_TBL_RATE_CTRL_INFO1 'd06
`define PLY_TBL_RATE_CTRL_INFO2 'd07
`define PLY_TBL_RATE_CTRL_INFO3 'd08
`define PLY_TBL_RATE_CTRL_INFO4 'd09
`define PLY_TBL_POWER_CTRL_INFO1 'd10
`define PLY_TBL_POWER_CTRL_INFO2 'd11
`define PLY_TBL_POWER_CTRL_INFO3 'd12
`define PLY_TBL_POWER_CTRL_INFO4 'd13

//READ WRITE CONTROLLER
// `define WORD                   'b10
`define HALF_WORD              'b01

//Read Write Controller defines
`define MAX_AHB_FETCH          'd16 //in quadlets
 

 
