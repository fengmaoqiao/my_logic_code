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
// Description      : upstream bus interface
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
// $HeadURL: $
//
//////////////////////////////////////////////////////////////////////////////

`define  RW_SIMU
module upstream_req_n_data
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire           clk,
  input  wire           rst_n,

  /*****************************************************************************
  * channel request
  *****************************************************************************/
  input  wire           channel_sel,
  input  wire           channel_req,
  input  wire [31:0]    channel_saddr,
  input  wire [31:0]    channel_daddr,
  input  wire [15:0]    channel_length,
  input  wire [ 3:0]    channel_tag,
  output wire           channel_busy,

  /*****************************************************************************
  * fragment parameters
  *****************************************************************************/
  output reg  [31:0]    src_addr,
  output reg  [31:0]    dst_addr,
  output reg  [15:0]    byte_length,

  /*****************************************************************************
  * aligner interface
  *****************************************************************************/
  output reg            busif_start,
  input  wire [63:0]    aligner_data,
  input  wire           aligner_data_en,
 
  /*****************************************************************************
  * Dini tohost interface
  *****************************************************************************/
  input  wire           tohost_almost_full,
  output reg  [63:0]    tohost_data,
  output reg  [ 7:0]    tohost_ctrl,
  output reg            tohost_valid
);

  /*****************************************************************************
  * declarations
  *****************************************************************************/
  /* flops */
  localparam  S_IDLE=2'b00,
              S_INIT=2'b01,
              S_DESC=2'b10,
              S_DATA=2'b11;
              
  reg  [ 1:0] state;
  reg  [ 3:0] tag;
  reg         is_first;
  reg  [15:0] count;
  
  
  
  /* wires */
  reg  [ 3:0] first_be;
  reg  [ 3:0] last_be;
  reg  [ 1:0] first_valid;
  reg  [ 1:0] last_valid;
  
  wire [15:0] nbr_dwordsx4;
  wire [ 1:0] dword_reliquat;
  wire [15:0] nbr_qwordsx8;
  wire [ 2:0] qword_reliquat;

  /*****************************************************************************
  * assignment
  *****************************************************************************/
  assign channel_busy = state!=S_IDLE;
  
  /*****************************************************************************
  * computes the number of dwords(32bits) involved in the transfer
  *****************************************************************************/
/*  assign dword_reliquat = byte_length[1:0] + 
                          dst_addr[1:0];
                          
  assign nbr_dwordsx4   = byte_length           +
                          {14'b0,dst_addr[1:0]} +
                          {13'b0,|dword_reliquat,2'b0};
*/                          
  assign dword_reliquat = byte_length[1:0] ;//+ 
                          //dst_addr[1:0];
                                                  
  assign nbr_dwordsx4   = byte_length           +
                          //{14'b0,dst_addr[1:0]} +
                          {13'b0,|dword_reliquat,2'b0};                          

  /*****************************************************************************
  * computes the number of qwords(64bits) involved in the transfer
  *****************************************************************************/
/*  assign qword_reliquat = byte_length[2:0] + 
                          dst_addr[2:0];
                          
  assign nbr_qwordsx8   = byte_length           +
                          {13'b0,dst_addr[2:0]} +
                          {12'b0,|qword_reliquat,3'b0};
*/  
    //去掉目的地址的影响后，64位的对齐就是传输字节长度取低3位                        
    assign qword_reliquat = byte_length[2:0]; //+ 
                            //dst_addr[2:0];
                          
    assign nbr_qwordsx8   = byte_length           +
                            //{13'b0,dst_addr[2:0]} +
                            {12'b0,|qword_reliquat,3'b0};
  
  /*****************************************************************************
  * computes leading/trailing byte enables
  *****************************************************************************/
  always @(*)
  begin
    //根据目的地址和传输数据长度决定第一次和最后一次的传输掩码
    case(dst_addr[1:0] & 2'b00)
      2'b00:  first_be = 4'b1111;
      2'b01:  first_be = 4'b1110;
      2'b10:  first_be = 4'b1100;
      default first_be = 4'b1000;
    endcase
    
    case(dword_reliquat)
      2'b00:  last_be  = 4'b1111;
      2'b01:  last_be  = 4'b0001;
      2'b10:  last_be  = 4'b0011;
      default last_be  = 4'b0111;
    endcase
    
    if(nbr_dwordsx4[15:2]==14'b1)
    begin
    
      first_be = first_be & last_be;
      last_be  = first_be;
      
    end
    
  end
      
  /*****************************************************************************
  * computes leading/trailing word enables
  *****************************************************************************/
  always @(*)
  begin
    //去掉上行通道目的地址的影响
    if(dst_addr[2] & 1'b0)
    
      first_valid = 2'b10;
      
    else
    
      first_valid = 2'b11;
      
    case(qword_reliquat)
    
      3'b000:   last_valid = 2'b11; 
      3'b001:   last_valid = 2'b01;
      3'b010:   last_valid = 2'b01;    
      3'b011:   last_valid = 2'b01;    
      3'b100:   last_valid = 2'b01;    
      3'b111:   last_valid = 2'b11;    
      3'b110:   last_valid = 2'b11;    
      default:  last_valid = 2'b11;    
    
    endcase
    
    if(nbr_qwordsx8[15:3]==13'b1)
    begin
    
      first_valid = first_valid & last_valid;
      last_valid  = first_valid;
      
    end
    
  end
  
  /*****************************************************************************
  * FSM
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin
  
    if(rst_n==1'b0)
    begin
    
      src_addr     <= 32'b0;
      dst_addr     <= 32'b0;
      byte_length  <= 16'b0;
      tag          <= 4'b0;

      busif_start  <= 1'b0;
      
      tohost_data  <= 64'b0;
      tohost_ctrl  <=  8'b0;
      tohost_valid <=  1'b0;
      
      count        <= 1'b0;
      
      is_first     <= 1'b0;

      state        <= S_IDLE;    
    
    end
    else
    begin
    
      case(state)
      
        S_IDLE:
        begin
        
          tohost_valid <= 1'b0;
          
          if(channel_sel & channel_req)
          begin
          
            src_addr    <= channel_saddr;
            dst_addr    <= channel_daddr;
            byte_length <= channel_length;
            tag         <= channel_tag;
            
            state       <= S_INIT;
          
          end
          
        end
        
        S_INIT:
        begin
        
          /* ensure that there is enough room in the tohost fifo before sending data */
          if(~tohost_almost_full)
          begin
          
          
            /* start bus interface */
            busif_start         <= 1'b1;
        
            /* descriptor 0 */
            tohost_data[63:32]  <= {24'b0,tag,4'b0};   // tag
            tohost_data[31]     <= 1'b1;               // valid
            tohost_data[30]     <= 1'b1;               // direction
            tohost_data[29:27]  <= 3'b0;               // reserved
            tohost_data[26]     <= 1'b1;             // byte enables enabled
            tohost_data[25:24]  <= 2'b0;               // reserved
            tohost_data[23:20]  <= first_be;         // first 32bits word byte enable
            tohost_data[19:16]  <= last_be;          // last 32bits word byte enable
            tohost_data[15: 0]  <= nbr_dwordsx4[15:2]; // number of 32 bits words involved in the transaction
          
            /* descriptor control */
            tohost_ctrl[7:5]    <= 3'b0; // not documented
            tohost_ctrl[4]      <= 1'b1; // descriptor enable
            tohost_ctrl[3]      <= 1'b0; // is last
            tohost_ctrl[2]      <= 1'b1; // demand-mode
            tohost_ctrl[1:0]    <= 2'b11; // validity of the 32bits parts of the 64bits word
          
            tohost_valid        <= 1'b1;
          
            state               <= S_DESC;
            
          end
        
        end
        
        S_DESC:
        begin
        
          tohost_data      <= {32'b0,dst_addr[31:2],2'b0};
          tohost_valid     <= 1'b1;
          
          is_first         <= 1'b1;
          count            <= nbr_qwordsx8[15:3];
          
          state            <= S_DATA;
        
        end
          
        default:
        begin
        
          /* data control */
          tohost_ctrl[7:5] <= 3'b0;  // not documented
          tohost_ctrl[4]   <= 1'b0;  // descriptor enable
          tohost_ctrl[3]   <= 1'b0;  // is last
          tohost_ctrl[2]   <= 1'b1;  // demand-mode
          tohost_ctrl[1:0] <= 2'b11; // validity of the 32bits parts of the 64bits word  
        
          if(aligner_data_en)
          begin
          
            is_first <= 1'b0;
            count    <= count - 1;
            
            if(count==1)
            begin
            
              /* last qword to be sent */
              tohost_ctrl[3] <= 1'b1;  // is last
              
              if(is_first)
                
                /* but is also the first word */
                tohost_ctrl[1:0] <= first_valid;
              
              else
              
                tohost_ctrl[1:0] <= last_valid;
                
              busif_start <= 1'b0;
              state       <= S_IDLE;
            
            end
            else
            begin
            
              if(is_first)
               
                tohost_ctrl[1:0] <= first_valid;
              
              else
                tohost_ctrl[1:0] <= 2'b11;
            
            end
            
            /* sent registered data */
            tohost_data  <= aligner_data;
            
            /* qword valid */
            tohost_valid <= 1'b1;
            
          end
          else
          begin
         
            /* qword invalid */
            tohost_valid <= 1'b0;
          
          end
        
        end
          
      endcase
    
    end
  
  end
 
  `ifdef RW_SIMU
  
    reg [16*8-1:0] state_str;
  
    always @(*)
    
      case (state)
      
        S_IDLE:   state_str = "S_IDLE";
        S_INIT:   state_str = "S_INIT";
        S_DESC:   state_str = "S_DESC";   
        S_DATA:   state_str = "S_DATA"; 
        default:  state_str = "UNDEF";
      endcase    
      
  `endif

endmodule

