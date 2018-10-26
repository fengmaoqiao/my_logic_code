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

//  This module provides an AHB slave interface to the RW-WLAN Core.

//  The external AHB master can access the operational registers and debug

//  registers of the W2LANMAC Core through this module.

// 

//  Supports only 32 bit read and writes.

//  Supports incrmenting bursts and single transfer.

//  Supports SPLIT response.

//  Does not support RETRY response.

//  Does not support lock transfers.

// 

//  One one side this module interface to AHB. On the other side it has a

//  register and FIFO read/write interface.

// 

//  If on the register interface the data is available combinationally with

//  address, then readyIn can be continuous. But in that case the hRData

//  assignment should be a continuous assignment.

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



`include "commonDefines.v"

`include "commonDefine.v"





`include "define.v"

`include "defineAHB.v"

`include "defineDMA.v"





`include "global_define.v"

module ahbSlaveIF (



      //$port_g clock and reset

      input wire                               hClk,           // AHB Clock ( ~120 MHz)                                               

      input wire                               hardRstHClk_n,  // AHB Reset signal.

      

      //$port_g AHB interface

      input wire                               hSelect,        // Select signal from external decoder. This is the trigger for the slave      

                                                               // to respond to transfers.                                                    

      input wire   [(`RW_HOST_ADDR_WIDTH-1):0] hAddr,          // Address for the transaction from external AHB master                        

      input wire                               hWrite,         // Control signal, 1-write transfer 0 -read transfer. From external AHB master 

      input wire   [1:0]                       hTrans,         // Transfer Type, from external AHB master                                     

                                                               // IDLE or BUSY or NON-SEQ or SEQ type of transfer                             

      input wire   [1:0]                       hSize,          // Size of each transfer, from external AHB master  (only 32 bits)             

      input wire   [(`RW_HOST_DATA_WIDTH-1):0] hWData,         // The data for the write transfer, from external AHB master                   

      input wire                               hReadyIn,       // This input indicates that the data transfer is complete                     

                                                               // on AHB. This is the global HREADYin signal for all Slaves                   

                                                               // indicates that the write can be completed in AHB by asserting hReady        

      output wire  [(`RW_HOST_DATA_WIDTH-1):0] hRData,         // Data read from the addressed register. Is valid when hReady is 1          

      output reg                               hReady,         // Ready signal. 1- transfer can complete, 0- the data phase to be extended. 

      output reg   [1:0]                       hResp,          // Transfer response for the initited transfer. Driven OKAY alwyas.          

                        

      //$port_g registers interface

      input wire   [(`RW_REG_DATA_WIDTH-1):0]  readDataIn,     // The read data from the addressed register.                                  

      input wire                               readyIn,        // Indicates that the register interface is ready for the transfer.            

                                                               // From register interface. When asserted for read transfers, indicates        

                                                               // that the data being read is present on readDataIn. For write transfers      

      input wire                               mibReadyIn,     // Indicates that the mib interface is ready for the transfer.



      output reg   [(`RW_REG_ADDR_WIDTH-1):0]  rdWrAddr,       // Address Offset of the register to be read or written                      

      output wire  [(`RW_REG_DATA_WIDTH-1):0]  writeDataOut,   // The data to be written into the addressed register                        

      output reg                               regWrite,       // addressed register to be written with data on writeDataOut             

      output reg                               regRead         // addressed register to be read and the read data should be given on     

                                                               // readDataIn along with readyIn                                            

);



  /*****************************************************************************

  * reg

  *****************************************************************************/

  reg                                   read_active ;

  reg                                   write_active;

  reg [(`RW_REG_ADDR_WIDTH-1):0]        waiting_address;

  reg                                   waiting_access;

  reg                                   waiting_type;



  /*****************************************************************************

  * output assignment

  *****************************************************************************/

  assign hRData        = readDataIn;

  assign writeDataOut  = hWData;

  



  /*****************************************************************************

  * AHB slave FSM

  *****************************************************************************/

  always @(posedge hClk,negedge hardRstHClk_n)

  begin

  

    if(hardRstHClk_n==1'b0) 

    begin

    

      rdWrAddr        <= `RW_REG_ADDR_WIDTH'b0;

      regWrite        <= 1'b0;

      regRead         <= 1'b0;

      //

      hResp           <= 2'b00;

      //

      waiting_address <= `RW_REG_ADDR_WIDTH'b0;

      waiting_access  <= 1'b0;

      waiting_type    <= 1'b0;

      //

      read_active     <= 1'b0;

      write_active    <= 1'b0;

    end

    else

    begin

      // access start

      if(hReadyIn && hSelect && (hTrans[1]==1'b1))

      begin

        // in case of length error, abort the access

        if (hSize != 2'b10)

        begin

          rdWrAddr  <= `RW_REG_ADDR_WIDTH'b0;

          regWrite  <= 1'b0;

          regRead   <= 1'b0;

          hResp     <= 2'b10;

        end   

        // AHB is triggered while register access ongoing then

        // bufferize access request and memorize the data   

        else if ((read_active || write_active) && !(readyIn && mibReadyIn) && hReady)

        begin

          waiting_address <= hAddr[15:2];

          waiting_access  <= 1'b1;

          waiting_type    <= hWrite;

          rdWrAddr        <= `RW_REG_ADDR_WIDTH'b0;

          regWrite        <= 1'b0;

          regRead         <= 1'b0;

          hResp           <= 2'b00;

          

        end

        // access is over, start buffurized access

        else if (waiting_access && (readyIn && mibReadyIn))

        begin

          rdWrAddr       <= waiting_address;

          regWrite       <= waiting_type;

          regRead        <= !waiting_type;

          write_active   <= waiting_type;

          read_active    <= !waiting_type;

          hResp          <= 2'b00;

          waiting_access <= 1'b0;

        end

        

        // register idle, start the access

        else if (hReady)

        begin

          rdWrAddr      <= hAddr[15:2];

          regWrite      <= hWrite;

          regRead       <= !hWrite;

          write_active  <= hWrite;

          read_active   <= !hWrite;

          hResp         <= 2'b00;

        end

        // access ongoing, clear the registers controls

        else 

        begin

          rdWrAddr        <= `RW_REG_ADDR_WIDTH'b0;

          regWrite        <= 1'b0;

          regRead         <= 1'b0;

          hResp           <= 2'b00;

        end

      end

      // access is over, start buffurized access

      else if (waiting_access && (readyIn && mibReadyIn))

      begin

        rdWrAddr       <= waiting_address;

        regWrite       <= waiting_type;

        regRead        <= !waiting_type;

        write_active   <= waiting_type;

        read_active    <= !waiting_type;

        hResp          <= 2'b00;

        waiting_access <= 1'b0;

      end

      // access is over clear the controls

      else if (readyIn && mibReadyIn)

      begin

        read_active   <= 1'b0;

        write_active  <= 1'b0;

        rdWrAddr      <= `RW_REG_ADDR_WIDTH'b0;

        regWrite      <= 1'b0;

        regRead       <= 1'b0;

        hResp         <= 2'b00;

      end

      // clear the controls

      else

      begin

        rdWrAddr  <= `RW_REG_ADDR_WIDTH'b0;

        regWrite  <= 1'b0;

        regRead   <= 1'b0;

        hResp     <= 2'b00;

      end

    end

  end



  /*****************************************************************************

  * Handle AHB slave hready

  *****************************************************************************/

  always @*

  begin

    if ((write_active || read_active ) && !mibReadyIn)

      hReady  = 1'b0;

    else if ( write_active && waiting_access && !waiting_type)

      hReady  = 1'b0;

    else if (waiting_access)

      hReady  = 1'b0;

      

    else if (read_active )

      hReady  = readyIn;

    else

      hReady  = 1'b1;

  

  end 

    

endmodule



//------------------- END OF FILE ----------------//

