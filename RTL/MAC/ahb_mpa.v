//////////////////////////////////////////////////////////////////////////////
//  Copyright (C) by RivieraWaves.
//  This module is a confidential and proprietary property of RivieraWaves
//  and a possession or use of this module requires written permission
//  from RivieraWaves.
//----------------------------------------------------------------------------
// $Author: jvanthou $
// Company          : RivieraWaves
//----------------------------------------------------------------------------
// $Revision: 16338 $
// $Date: 2014-10-03 10:45:11 +0200 (Fri, 03 Oct 2014) $
// ---------------------------------------------------------------------------
// Dependencies     : None
// Description      : Top level of ahb_mpa module
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
// $HeadURL: https://svn.frso.rivierawaves.com/svn/rw_wlan_nx/trunk/Projects/WLAN_NX_REF_IP/HW/SB/ahb_mpa/verilog/rtl/ahb_mpa.v $
//
//////////////////////////////////////////////////////////////////////////////


module ahb_mpa
#(
  /*****************************************************************************
  * AHB addres bus length (byte address)
  *****************************************************************************/
  parameter g_addr_width=17
)
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire                    clk,
  input  wire                    rst_n,

  /*****************************************************************************
  * AHB Slave 0 bus 
  *****************************************************************************/
  input  wire                    s0_hready_in,
  input  wire                    s0_hsel,
  input  wire [g_addr_width-1:0] s0_haddr,
  input  wire [ 1:0]             s0_htrans,
  input  wire                    s0_hwrite,
  input  wire [ 1:0]             s0_hsize,      
  input  wire [31:0]             s0_hwdata,
  output reg  [31:0]             s0_hrdata,
  output reg  [ 1:0]             s0_hresp,
  output reg                     s0_hready,
 
  /*****************************************************************************
  * AHB Slave 1 bus 
  *****************************************************************************/
  input  wire                    s1_hready_in,
  input  wire                    s1_hsel,
  input  wire [g_addr_width-1:0] s1_haddr,
  input  wire [ 1:0]             s1_htrans,
  input  wire                    s1_hwrite,
  input  wire [ 1:0]             s1_hsize,      
  input  wire [31:0]             s1_hwdata,
  output reg  [31:0]             s1_hrdata,
  output reg  [ 1:0]             s1_hresp,
  output reg                     s1_hready,
 
  /*****************************************************************************
  * AHB Master bus 
  *****************************************************************************/
  output wire                     m_hready_in,
  output  reg                     m_hsel,
  output  reg  [g_addr_width-1:0] m_haddr,
  output  wire [ 1:0]             m_htrans,
  output  reg                     m_hwrite,
  output  reg  [ 1:0]             m_hsize,      
  output  reg  [31:0]             m_hwdata,
  input   wire [31:0]             m_hrdata,
  input   wire [ 1:0]             m_hresp,
  input   wire                    m_hready

);

//////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////
// Internal Wires declarations
//////////////////////////////////////////////////////////////////////////////

wire [1:0] request;
reg  [1:0] owner;
reg  [1:0] previous_owner;
reg  [1:0] pending;
reg        lock;

reg [g_addr_width-1:0] haddr_hold;
reg                    hwrite_hold;
reg              [1:0] hsize_hold;

reg              [1:0] m_htrans_i;


//////////////////////////////////////////////////////////////////////////////
// Begining of Logic part
//////////////////////////////////////////////////////////////////////////////
assign  m_htrans    = m_htrans_i;
assign  m_hready_in = m_hready;

//////////////////////////////////
// m_htrans / m_hsel generation
//////////////////////////////////
always @*
begin
  if (owner != 2'b00)
  begin
    if (owner[0] == 1'b1)
    begin
      if (pending[0] == 1'b1)
      begin
        m_hsel     = 1'b1;
        m_htrans_i = 2'b10;
      end
      else if (s0_hsel == 1'b1)
      begin
        m_hsel     = 1'b1;
        m_htrans_i = s0_htrans;
      end
      else
      begin
        m_hsel     = 1'b0;
        m_htrans_i = 2'b00;
      end
    end
    else
    begin
      if (pending[1] == 1'b1)
      begin
        m_hsel     = 1'b1;
        m_htrans_i = 2'b10;
      end
      else if (s1_hsel == 1'b1)
      begin
        m_hsel     = 1'b1;
        m_htrans_i = s1_htrans;
      end
      else
      begin
        m_hsel     = 1'b0;
        m_htrans_i = 2'b00;
      end  
    end
  end
  else
  begin
    m_hsel     = 1'b0;
    m_htrans_i = 2'b00;
  end
end




//////////////////////////////////
// AHB control mux : 
// asymetric mux minimizing AHB0 paths
//////////////////////////////////
always @*
begin
  if (owner != 2'b00)
  begin
    if (owner[0] == 1'b1)
    begin
      if (pending[0] == 1'b1)
      begin
        m_haddr   = haddr_hold; 
        m_hwrite  = hwrite_hold;
        m_hsize   = hsize_hold; 
      end
      else
      begin
        m_haddr   = s0_haddr;    
        m_hwrite  = s0_hwrite;   
        m_hsize   = s0_hsize;    
      end
    end  
    else
    begin
      if (pending[1] == 1'b1)
      begin
        m_haddr   = haddr_hold; 
        m_hwrite  = hwrite_hold;
        m_hsize   = hsize_hold; 
      end
      else
      begin
        m_haddr   = s1_haddr;    
        m_hwrite  = s1_hwrite;   
        m_hsize   = s1_hsize;    
      end
    end
  end
  else
  begin  
    m_haddr   = 'b0;
    m_hwrite  = 1'b0;
    m_hsize   = 'b0;
  end
end
 

//////////////////////////////////
// AHB data mux : 
// asymetric structure minimizing AHB0 paths
//////////////////////////////////

always @*
begin
  
  if (previous_owner == 2'b01)
  begin
    s0_hrdata = m_hrdata;
    s0_hresp  = m_hresp;
    s0_hready = m_hready;

    s1_hrdata = 32'b0;
    s1_hresp  = 2'b00;
    s1_hready = !pending[1];

    m_hwdata  = s0_hwdata;
  end
  else if (previous_owner == 2'b10)
  begin  
    s0_hrdata = 32'b0;
    s0_hresp  = 2'b00;
    s0_hready = !pending[0];

    s1_hrdata = m_hrdata;
    s1_hresp  = m_hresp;
    s1_hready = m_hready;

    m_hwdata  = s1_hwdata;
  end  
  else
  begin  
    s0_hrdata = 32'b0;
    s0_hresp  = 2'b00;
    s0_hready = 1'b1;

    s1_hrdata = 32'b0;
    s1_hresp  = 2'b00;
    s1_hready = 1'b1;

    m_hwdata  = 32'b0;
  end
  end

//////////////////////////////////
// AHB control hold  
//////////////////////////////////
always @(posedge clk , negedge rst_n)
begin
   
  if(rst_n==1'b0)
  begin
    haddr_hold  <= 'b0;
    hwrite_hold <= 1'b0;
    hsize_hold  <= 2'b0;
//     hburst_hold <= 2'b0;
//     hprot_hold  <= 2'b0;

    pending     <= 2'b0;
  end   
  else
  begin

    // S0 Access requested
    if (request[0] == 1'b1)
    begin    
      if (owner[0] == 1'b0)
      begin
        haddr_hold  <= s0_haddr;
        hwrite_hold <= s0_hwrite;
        hsize_hold  <= s0_hsize;
//         hburst_hold <= s0_hburst;
//         hprot_hold  <= s0_hprot;
        pending[0]  <= 1'b1;
      end  
      else
        pending[0]  <= 1'b0;
    end
    else
    begin
      if (owner[0] == 1'b1)
        if (pending[0] == 1'b1)
          pending[0] <= 1'b0;
    end
        
    // S1 Access requested
    if (request[1] == 1'b1)
    begin 
      if (owner[1] == 1'b0)
      begin
        haddr_hold  <= s1_haddr;
        hwrite_hold <= s1_hwrite;
        hsize_hold  <= s1_hsize;
//         hburst_hold <= s1_hburst;
//         hprot_hold  <= s1_hprot;
        pending[1]  <= 1'b1;
      end 
      else
        pending[1]  <= 1'b0;
    end
    else
    begin 
      if (owner[1] == 1'b1)
        if (pending[1] == 1'b1)
          pending[1] <= 1'b0;
    end
  end
end



assign request[0] = ((s0_hready_in == 1'b1) && (s0_hsel == 1'b1) && (s0_htrans == 2'b10)) ? 1'b1 : 1'b0;
assign request[1] = ((s1_hready_in == 1'b1) && (s1_hsel == 1'b1) && (s1_htrans == 2'b10)) ? 1'b1 : 1'b0;


//////////////////////////////////
// owner generation
//////////////////////////////////

always @*
begin
  if (lock == 1'b0)
  begin
    if (pending != 2'b00)
    begin
      if (pending[0] == 1'b1)
        owner <= 2'b01;
      else
        owner <= 2'b10;
    end    
    else
    begin
      if (request != 2'b00)
      begin
        if (request[0] == 1'b1)
          owner <= 2'b01;
        else 
          owner <= 2'b10;
      end  
      else
        owner <= 2'b00;
    end
  end  
  else // if lock == 1'b1
    owner <= previous_owner;
end


//////////////////////////////////
// lock generation
//////////////////////////////////

always @(posedge clk , negedge rst_n)
begin
   
  if (rst_n==1'b0)
  begin
    previous_owner <= 2'b00;
    lock           <= 1'b0;
  end  
  else if (m_hready == 1'b1)
  begin
    if (lock == 1'b0)
    begin
      if (m_htrans_i == 2'b10)
      begin
        previous_owner <= owner;
        lock           <= 1'b1;
      end
    end  
    else
    begin
      if (m_htrans_i == 2'b00)
        lock <= 1'b0;
    end
  end
end


endmodule
                 
//////////////////////////////////////////////////////////////////////////////
// End of file
//////////////////////////////////////////////////////////////////////////////
