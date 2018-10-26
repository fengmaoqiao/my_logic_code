//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : dma_ctrl.sv
// Author      : qiupeng
// E_mail      : qiupeng@outwitcom.com
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$
//
//
//**********************************************************


`define  RW_SIMU
module dma_ctrl
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input wire                       clk,
  input wire                       rst_n,

  /*****************************************************************************
  * Interrupts
  *****************************************************************************/
  output wire [15:0]               lli_irq,
  output wire [ 3:0]               channel_irq,
  output wire                      error_irq,
  
  /*****************************************************************************
  * register bank interface
  *****************************************************************************/
  input  wire                      hready_in_regb,
  input  wire                      hsel_regb,
  input  wire [ 7:0]               haddr_regb,
  input  wire [ 1:0]               htrans_regb,
  input  wire                      hwrite_regb,
  output reg  [31:0]               hrdata_regb,
  input  wire [31:0]               hwdata_regb,
  output wire                      hready_regb,
  output wire [ 1:0]               hresp_regb,

  /*****************************************************************************
  * LLI AHB master interface
  *****************************************************************************/
  input  wire                      hready_lli,
  output reg  [31:0]               haddr_lli,
  output reg  [ 1:0]               htrans_lli,
  output wire                      hwrite_lli,
  input  wire [31:0]               hrdata_lli,
  input  wire [ 1:0]               hresp_lli,

  /*****************************************************************************
  * physical channel interface
  *
  *   channel 0 & 1 are upstream channels (data movment from embeded to host)
  *   channel 2 & 3 are downstream channels (data movment from host to embedded)
  *
  *****************************************************************************/
  // fragment request
  output reg                       channel_dir,   // 0:upstream / 1:downstream
  output reg                       channel_req,
  
  // fragment request parameters
  output reg  [31:0]               channel_saddr,
  output reg  [31:0]               channel_daddr,
  output reg  [15:0]               channel_length, // byte length
  output reg  [ 3:0]               channel_tag,
  
  // upstream physical busy, can't accept request
  input  wire                      upstream_busy, 
  
  // upstream physical channel acknowledge 
  input  wire                      upstream_ack,
  input  wire [ 3:0]               upstream_ack_tag,
  input  wire [15:0]               upstream_ack_length, // dword length
  output reg                       upstream_ack_ack,
  
  // upstream physical busy, can't accept request
  input  wire                      downstream_busy,
  
  // associated address, requried if data are returned out-of-order 
  output wire [ 2:0]               downstream_oft_saddr,
  output wire [31:0]               downstream_oft_daddr,
  output wire [15:0]               downstream_oft_length, // byte length
  
  // upstream physical channel acknowledge 
  input  wire                      downstream_ack,
  input  wire [ 3:0]               downstream_ack_tag,
  input  wire [15:0]               downstream_ack_length, // dword length
  output reg                       downstream_ack_ack,
  
  output reg  [2:0]  channel_if_add_data
);

  /*****************************************************************************
  * request state machine declaration
  *****************************************************************************/
  /* request state machine */
  localparam  S_IDLE=3'd0,     
              S_LLI_ADDR=3'd1, 
              S_LLI_D0=3'd2,   
              S_LLI_D1=3'd3,   
              S_LLI_D2=3'd4,   
              S_LLI_D3=3'd5,   
              S_REQUEST=3'd6,
              S_ACCEPT=3'd7;  
  reg [ 2:0] request_state;
  
  /*****************************************************************************
  * spin lock declaration
  *****************************************************************************/
  /* indicates the lli walker shall not process the descriptor having a null
     next pointer */
  reg [ 3:0] ch_mutex;    // indicates that the lli walker shall stop the 
  
  /* indicates the lli walker has reached a descriptor having a null
     next pointer, so the logical channel is stalled until it is released
     by the software  */
  reg [ 3:0] ch_stopped;
  
  /*****************************************************************************
  * arbitration declaration
  *****************************************************************************/
  /* indicates logical channel and priority for the lli walking */
  reg [ 1:0] lli_channel;
  reg [ 1:0] lli_pri_level;
  
  /* indciates that there is a valid request for lli walker */
  wire       arb_valid;
  
  /* indciates the logical number and priority of the highest valid queue entry */
  wire [1:0] arb_channel;
  wire [1:0] arb_level;
  
  
  /* priority queue */
  reg [1:0]  arb_q0;       /* logical channel number with highest priority */ 
  wire       arb_q0_valid; /* entry is valid for lli walker */ 
  
  reg [1:0]  arb_q1; 
  wire       arb_q1_valid; 
  
  reg [1:0]  arb_q2; 
  wire       arb_q2_valid; 
        
  reg [1:0]  arb_q3;      /* lowest priority */
  wire       arb_q3_valid; 

  reg  [3:0] downstream_tag_released;
  reg  [3:0] downstream_tag_taken;   
  reg  [3:0] downstream_tag_limit;
  wire       downstream_limit_reached;     

  /*****************************************************************************
  * interrupts declaration
  *****************************************************************************/
  reg [ 3:0] channel_irq_pending;
  reg [ 3:0] channel_irq_mask;
  reg [15:0] lli_irq_pending;
  reg [15:0] lli_irq_mask;
  reg        error_irq_pending;
  reg        error_irq_mask;
  
  /* lli root */
  reg [31:0] ch_lli_root[0:3];
  
  /* lli counters*/
  reg [15:0] lli_counter[0:15];

  /* lli AHB */
  reg [31:0] hrdata_lli_1t;
  reg        htrans_lli_1t;
  
  /* tempory registers */
  reg [5:0]  regb_addr;
  reg        regb_write_pending;
  reg [3:0]  oft_readback_addr;
  
  /*****************************************************************************
  * outstanding fragment table declaration
  *****************************************************************************/
  reg [ 3:0] oft_free_entry;
  reg [15:0] oft_free;
  reg [15:0] oft_lli_counter_en;
  reg [15:0] oft_lli_irq_en;
  reg        oft_eof_irq_en[0:15];
  reg  [1:0] oft_eof_irq_no[0:15];
  reg [15:0] oft_length[0:15];
  reg [ 3:0] oft_lli_counter_no[0:15];
  reg [ 3:0] oft_lli_irq_no[0:15];
  reg [31:0] oft_daddr[0:15];
  reg [31:0] oft_saddr[0:15];
   
  /*****************************************************************************
  * misc wires declaration
  *****************************************************************************/
  wire [1:0]  host_addr_offset;
  wire [1:0]  host_reliquat;
  wire [15:0] nbr_dwordsx4;
  reg  [15:0] ack_length;
  reg  [ 3:0] ack_tag;
  
  
  
  /*****************************************************************************
  * assignments
  *****************************************************************************/
  assign hwrite_lli  = 1'b0;
  assign hready_regb = 1'b1;
  assign hresp_regb  = 2'b00;
  
  /*****************************************************************************
  * interrupt lines
  *****************************************************************************/
  assign channel_irq = channel_irq_pending & channel_irq_mask;
  assign lli_irq     = lli_irq_pending     & lli_irq_mask;
  assign error_irq   = error_irq_pending   & error_irq_mask;
  
  /*****************************************************************************
  * physical channel acknowledge arbitration
  *****************************************************************************/
  always @(*)
  begin
    /* default values */
    ack_tag            = downstream_ack_tag;
    ack_length         = downstream_ack_length;
    downstream_ack_ack = 1'b0;
    upstream_ack_ack   = 1'b0;
    /* we can process one acknowledeg at once, if the 
       two physical channel acknowledge occurs, then
       arbitrarely process downstream first */
    if(downstream_ack==1'b1)
    begin
      downstream_ack_ack = 1'b1;
    end
    else if(upstream_ack==1'b1)
    begin
      ack_tag          = upstream_ack_tag;
      ack_length       = upstream_ack_length;
      upstream_ack_ack = 1'b1;
    end
  end  

  /* some maths to determine the quantity of 32 bits words
  * effectively transfered. See math.pl for more understanding
  */
  assign host_addr_offset = oft_saddr[ack_tag][1:0] & {2{downstream_ack_ack}} |
                            oft_daddr[ack_tag][1:0] & {2{upstream_ack_ack}};
  
  assign host_reliquat    = host_addr_offset + oft_length[ack_tag][1:0];
  assign nbr_dwordsx4     = oft_length[ack_tag] +
                            {14'b0,host_addr_offset} +
                            {13'b0,|host_reliquat,2'b0};

  /*****************************************************************************
  * select a free OST entry
  *****************************************************************************/
  always @(*)
    if(oft_free[15:8]!=0)       
      if(oft_free[15:12]!=0)    
        casez(oft_free[15:12])
          4'bzzz1: oft_free_entry <= 4'b1100;
          4'bzz10: oft_free_entry <= 4'b1101;
          4'bz100: oft_free_entry <= 4'b1110;
          default: oft_free_entry <= 4'b1111;                       
        endcase              
      else                      
        casez(oft_free[11:8])
          4'bzzz1: oft_free_entry <= 4'b1000;
          4'bzz10: oft_free_entry <= 4'b1001;
          4'bz100: oft_free_entry <= 4'b1010;
          default: oft_free_entry <= 4'b1011;                       
        endcase              
    else                        
      if(oft_free[7:4]!=0)    
        casez(oft_free[7:4])
          4'bzzz1: oft_free_entry <= 4'b0100;
          4'bzz10: oft_free_entry <= 4'b0101;
          4'bz100: oft_free_entry <= 4'b0110;
          default: oft_free_entry <= 4'b0111;                       
        endcase              
      else                      
        casez(oft_free[3:0])
          4'bzzz1: oft_free_entry <= 4'b0000;
          4'bzz10: oft_free_entry <= 4'b0001;
          4'bz100: oft_free_entry <= 4'b0010;
          default: oft_free_entry <= 4'b0011;                       
        endcase              

  /*****************************************************************************
  * OST read back address for downstream physical channel 
  *****************************************************************************/
  assign downstream_oft_saddr  = oft_saddr[downstream_ack_tag][2:0];
  assign downstream_oft_daddr  = oft_daddr[downstream_ack_tag];
  assign downstream_oft_length = oft_length[downstream_ack_tag];


  /*****************************************************************************
  * channel arbitration
  *****************************************************************************/
  /* avoid tag starvation caused by downstream 
   * 'limit'=0 means disabled
  */
  assign downstream_limit_reached = (downstream_tag_limit == (downstream_tag_taken - downstream_tag_released)) &&
                                    downstream_tag_limit!=4'b0;
  
  
  /* indicates which arbitration queue entry is valid
   * An entry is valid if 1) there are enough tag for a given physical channel
   *                      2) the corresponding root pointer is non-null 
   *                      3) the channel is not stopped by a semaphore
   *                      4) the corresponding physical channel is ready for request
   */
  assign arb_q0_valid = ch_lli_root[arb_q0]!=32'b0 && 
                        ch_stopped[arb_q0]==1'b0 && 
                        (arb_q0[1]==1'b0 && upstream_busy==1'b0 || arb_q0[1]==1'b1 && downstream_busy==1'b0 && downstream_limit_reached==1'b0);

  assign arb_q1_valid = ch_lli_root[arb_q1]!=32'b0 && 
                        ch_stopped[arb_q1]==1'b0 && 
                        (arb_q1[1]==1'b0 && upstream_busy==1'b0 || arb_q1[1]==1'b1 && downstream_busy==1'b0 && downstream_limit_reached==1'b0);

  assign arb_q2_valid = ch_lli_root[arb_q2]!=32'b0 && 
                        ch_stopped[arb_q2]==1'b0 && 
                        (arb_q2[1]==1'b0 && upstream_busy==1'b0 || arb_q2[1]==1'b1 && downstream_busy==1'b0 && downstream_limit_reached==1'b0);

  assign arb_q3_valid = ch_lli_root[arb_q3]!=32'b0 && 
                        ch_stopped[arb_q3]==1'b0 && 
                        (arb_q3[1]==1'b0 && upstream_busy==1'b0 || arb_q3[1]==1'b1 && downstream_busy==1'b0 && downstream_limit_reached==1'b0);
  
  /*  priority decoder*/
  assign arb_valid               =  arb_q0_valid | arb_q1_valid | arb_q2_valid | arb_q3_valid;

  assign {arb_channel,arb_level} = {arb_q0,2'b00} & {4{arb_q0_valid}} |
                                   {arb_q1,2'b01} & {4{~arb_q0_valid & arb_q1_valid}} |
                                   {arb_q2,2'b10} & {4{~arb_q0_valid & ~arb_q1_valid & arb_q2_valid}} |
                                   {arb_q3,2'b11} & {4{~arb_q0_valid & ~arb_q1_valid & ~arb_q2_valid & arb_q3_valid}};
                                
  /*****************************************************************************
  * Register Bank
  *
  * 0  RW  0x00  ch_lli_root[0]
  * 1  RW  0x04  ch_lli_root[1]
  * 2  RW  0x08  ch_lli_root[2]
  * 3  RW  0x0C  ch_lli_root[3]
  * 4  RW  0x10  dma_status
  * 5  RW  0x14  int_raw_status
  * 6  RW  0x18  int_unmask_set
  * 7  RW  0x1C  int_unmask_clear
  * 8  RW  0x20  int_ack
  * 9  R   0x24  int_status
  * 13 RW  0x34  arbitration
  * 14 RW  0x38  channel_mutex_set
  * 15 RW  0x3C  channel_mutex_clear
  * 32 RW  0x80  lli_counter[0]
  *    "         up to
  * 47 RW  0xbc  lli_counter[15]
  *
  *****************************************************************************/
  /*****************************************************************************
  * main state machine
  *****************************************************************************/
  always @(posedge clk, negedge rst_n)
  begin:b_main_fsm
  
    integer    v_i;
    
    if(rst_n==1'b0)
    begin
      
      /* interrupts */
      lli_irq_pending     <= 16'b0;         
      error_irq_pending   <= 1'b0;          
      channel_irq_pending <= 4'b0;             
      lli_irq_mask        <= 0;             
      error_irq_mask      <= 0;
      channel_irq_mask    <= 4'b0;             

      /* request fsm */
      request_state       <= S_IDLE;      
      ch_mutex            <= 4'b0;   
      ch_stopped          <= 4'b0;   
      ch_lli_root[0]      <= 32'b0;
      ch_lli_root[1]      <= 32'b0;
      ch_lli_root[2]      <= 32'b0;
      ch_lli_root[3]      <= 32'b0;
      
      /* arbitration */
      lli_channel         <= 2'b00;
      lli_pri_level       <= 2'b00;
      
      arb_q0              <= 2'b00;
      arb_q1              <= 2'b10;
      arb_q2              <= 2'b01;
      arb_q3              <= 2'b11;
      
      downstream_tag_released <= 4'b0000;
      downstream_tag_taken    <= 4'b0000;
      downstream_tag_limit    <= 4'b1100;

      /* AHB lli master */
      haddr_lli           <= 0;
      htrans_lli          <= 0;
      htrans_lli_1t       <= 0;
      hrdata_lli_1t       <= 32'b0;
      
      /* fragment parameters */
      channel_dir         <= 1'b0;
      channel_req         <= 1'b0;
      channel_saddr       <= 32'b0;
      channel_daddr       <= 32'b0;
      channel_length      <= 16'b0;
      channel_tag         <= 4'b0;
      
      for(v_i=0;v_i<16;v_i=v_i+1)
      begin
      
        /* lli counters and interrupts */
        lli_counter[v_i]     <= 0;
        lli_irq_pending[v_i] <= 0;
        /* OST */
        oft_free[v_i]           <= 1'b1;
        oft_lli_counter_en[v_i] <= 1'b0;
        oft_lli_counter_no[v_i] <= 4'b0;
        oft_lli_irq_en[v_i]     <= 1'b0;
        oft_lli_irq_no[v_i]     <= 4'b0;
        oft_length[v_i]         <= 16'b0;
        oft_eof_irq_en[v_i]     <= 1'b0;
        oft_eof_irq_no[v_i]     <= 4'b0;
        oft_saddr[v_i]          <= 32'b0;
        oft_daddr[v_i]          <= 32'b0;
      
      end
      
      /* registers */
      regb_write_pending        <= 1'b0;
      regb_addr                 <= 6'b0;
      hrdata_regb               <= 32'b0;
      oft_readback_addr         <= 4'b0;    
     
      /* wires, not register */
      v_i          = 0;
    end
    else
    begin
      v_i          = 0;
      /*************************************************************************
      * AHB write access
      *************************************************************************/
      if(regb_write_pending)
      begin
        regb_write_pending <= 1'b0;
        casez(regb_addr)
          /*********************************************************************
          * channel0_lli_root
          *********************************************************************/
          6'd0:
          begin
            ch_lli_root[0] <= hwdata_regb;
            ch_mutex[0]    <= 1'b0;
            ch_stopped[0]  <= 1'b0;
          end
          /*********************************************************************
          * channel1_lli_root
          *********************************************************************/
          6'd1:
          begin
            ch_lli_root[1] <= hwdata_regb;
            ch_mutex[1]    <= 1'b0;
            ch_stopped[1]  <= 1'b0;
          end
          /*********************************************************************
          * channel2_lli_root
          *********************************************************************/
          6'd2:
          begin
            ch_lli_root[2] <= hwdata_regb;
            ch_mutex[2]    <= 1'b0;
            ch_stopped[2]  <= 1'b0;
          end
          /*********************************************************************
          * channel3_lli_root
          *********************************************************************/
          6'd3:
          begin
            ch_lli_root[3] <= hwdata_regb;
            ch_mutex[3]    <= 1'b0;
            ch_stopped[3]  <= 1'b0;
          end
          /***********************************************************************        
          * dma_status                                                                    
          ***********************************************************************/        
          6'd4:                                                                           
          begin                                                                           
            if(hwdata_regb[31:16]==16'h5a6f) 
              oft_free <= hwdata_regb[15:0];
          end                                                                             
          /*********************************************************************
          * int_unmask_set
          *********************************************************************/
          6'd6:
          begin
            lli_irq_mask     <= lli_irq_mask     | hwdata_regb[15:0];
            error_irq_mask   <= error_irq_mask   | hwdata_regb[16];
            channel_irq_mask <= channel_irq_mask | hwdata_regb[23:20];
          end
          /*********************************************************************
          * int_unmask_clear
          *********************************************************************/
          6'd7:
          begin
            lli_irq_mask     <= lli_irq_mask     & ~hwdata_regb[15:0];
            error_irq_mask   <= error_irq_mask   & ~hwdata_regb[16];
            channel_irq_mask <= channel_irq_mask & ~hwdata_regb[23:20];
          end
          /*********************************************************************
          * int_ack
          *********************************************************************/
          6'd8:
          begin
            lli_irq_pending     <= lli_irq_pending     & ~hwdata_regb[15:0];
            error_irq_pending   <= error_irq_pending   & ~hwdata_regb[16];
            channel_irq_pending <= channel_irq_pending & ~hwdata_regb[23:20];
          end
          /*********************************************************************
          * arbitration
          *********************************************************************/
          6'd13:
          begin
            downstream_tag_limit <= hwdata_regb[3:0];
          end
          /*********************************************************************
          * channel_mutex_set
          *********************************************************************/
          6'd14:
          begin
            ch_mutex    <= ch_mutex | hwdata_regb[3:0];
          end
          /*********************************************************************
          * channel_mutex_clear
          *********************************************************************/
          6'd15:
          begin
            ch_mutex    <= ch_mutex   & ~hwdata_regb[3:0];
            ch_stopped  <= ch_stopped & ~hwdata_regb[3:0];
          end
          /***********************************************************************
          * lli0_counter
          ***********************************************************************/
          6'b10????: lli_counter[regb_addr[3:0]]  <= 16'b0;
          /***********************************************************************
          * debug
          ***********************************************************************/
          6'b110000: oft_readback_addr  <= hwdata_regb[3:0];
          /*********************************************************************
          * RESERVED
          *********************************************************************/
          default: ;
        endcase
      end
      
      /*************************************************************************
      * AHB read access
      *************************************************************************/
      hrdata_regb <= 32'b0;
      if(hready_in_regb==1'b1 & htrans_regb[1]==1'b1 && hsel_regb==1'b1)
      begin
        if(hwrite_regb==1'b0)
        begin
          casez(haddr_regb[7:2])
            /***********************************************************************
            * channel0_lli_root
            ***********************************************************************/
            6'd0: hrdata_regb <= ch_lli_root[0];
            /***********************************************************************
            * channel1_lli_root
            ***********************************************************************/
            6'd1: hrdata_regb <= ch_lli_root[1];
            /***********************************************************************
            * channel2_lli_root
            ***********************************************************************/
            6'd2: hrdata_regb <= ch_lli_root[2];
            /***********************************************************************
            * channel3_lli_root
            ***********************************************************************/
            6'd3: hrdata_regb <= ch_lli_root[3];
            /***********************************************************************
            * dma_status
            ***********************************************************************/
            6'd4:
            begin
              hrdata_regb[29:28] <= {downstream_busy,upstream_busy};
              hrdata_regb[27:24] <= {arb_q3_valid,arb_q2_valid,arb_q1_valid,arb_q0_valid};
              hrdata_regb[23:20] <= request_state;
              hrdata_regb[19:16] <= ch_stopped;
              hrdata_regb[15:0]  <= oft_free;
            end
            /***********************************************************************
            * int_raw_status (show state of interrupt line whatever the mask)
            ***********************************************************************/
            6'd5: 
            begin
              hrdata_regb[15:0]  <= lli_irq_pending;
              hrdata_regb[16]    <= error_irq_pending;
              hrdata_regb[23:20] <= channel_irq_pending; 
            end
            /***********************************************************************
            * int_unmask_set,int_unmask_clear
            ***********************************************************************/
            6'd6,6'd7: 
            begin
              hrdata_regb[15:0]  <= lli_irq_mask;
              hrdata_regb[16]    <= error_irq_mask;
              hrdata_regb[23:20] <= channel_irq_mask; 
            end
       
            /***********************************************************************
            * int_status (show the state of the enabled pending interrupt line)
            ***********************************************************************/
            6'd9: 
            begin
              hrdata_regb[15:0]  <= lli_irq_pending     & lli_irq_mask;
              hrdata_regb[16]    <= error_irq_pending   & error_irq_mask;
              hrdata_regb[23:20] <= channel_irq_pending & channel_irq_mask; 
            end
            
            /*********************************************************************
            * arbitration
            *********************************************************************/
            6'd13:
            begin
              hrdata_regb[3:0] <= downstream_tag_limit;
            end
       
            /***********************************************************************
            * channel_mutex_set, channel_mutex_clear
            ***********************************************************************/
            6'd14,6'd15:
            begin
              hrdata_regb[3:0] <= ch_mutex[3:0];
            end
            
            /***********************************************************************
            * lli_counter[0:15]
            ***********************************************************************/
            6'b10????: hrdata_regb[15:0] <= lli_counter[haddr_regb[5:2]];
            /***********************************************************************
            * debug
            ***********************************************************************/
            6'b110000: hrdata_regb[ 3:0] <= oft_readback_addr;
            6'b110001: hrdata_regb[31:0] <= oft_saddr[oft_readback_addr];
            6'b110010: hrdata_regb[31:0] <= oft_daddr[oft_readback_addr];
            6'b110011: hrdata_regb[15:0] <= oft_length[oft_readback_addr];
            6'b110100: hrdata_regb[13:0] <= {oft_lli_counter_en[oft_readback_addr], 
                                             oft_lli_irq_en[oft_readback_addr],   
                                             oft_eof_irq_en[oft_readback_addr],   
                                             oft_eof_irq_no[oft_readback_addr], 
                                             oft_lli_counter_no[oft_readback_addr],
                                             oft_lli_irq_no[oft_readback_addr]};

            /***********************************************************************
            * default
            ***********************************************************************/
            default: ;
          endcase
        end
        else
        begin
          regb_write_pending <= 1'b1;
          regb_addr          <= haddr_regb[7:2];
        end
      end

      /*************************************************************************
      * interrupt and lli counter managment
      *
      * Note to maintiner: ensure this block is always after the AHB write one
      *  to prevent race contion for concurrent (HW set/SW clear) of irqs.
      *************************************************************************/
      if(downstream_ack_ack | upstream_ack_ack)
      begin
        if(ack_length==nbr_dwordsx4[15:2] && oft_free[ack_tag]==1'b0)
        begin
          /* the system has read or write the expected number of bytes */
          if(oft_lli_counter_en[ack_tag]==1'b1)
          begin
            /* update lli counters */
            lli_counter[oft_lli_counter_no[ack_tag]] <= lli_counter[oft_lli_counter_no[ack_tag]] + 16'h0001;
          end
          if(oft_lli_irq_en[ack_tag]==1'b1)
          begin
            /* update lli interrupt */
            lli_irq_pending[oft_lli_irq_no[ack_tag]] <= 1'b1;
          end
          if(oft_eof_irq_en[ack_tag]==1'b1)
          begin
            /* update lli interrupt */
            channel_irq_pending[oft_eof_irq_no[ack_tag]] <= 1'b1;
          end
        end
        else
        begin
          /* something went wrong with physical channel
           *
           * can be
           *  1) a ack descriptor is returned while the corresponding OFT entry is free
           *  2) a ack descriptor is returned with a unexpected length
           */
          error_irq_pending <= 1'b1;
        
          $display("error: ack descriptor mismatch !");
          $display("  ack_tag         = %x",ack_tag);
          $display("  ack_length      = %x",ack_length);
          $display("  expected dwords = %x",nbr_dwordsx4[15:2]);
          $display("  oft_free[%x]    = %x",ack_tag,oft_free[ack_tag]);
          $stop();
        
        end
        
        /* free the ost entry */
        oft_free[ack_tag] <= 1'b1;
        
        /* increment release counter for downstream */
        if(downstream_ack_ack)
        
          downstream_tag_released <= downstream_tag_released + 4'd1;
        
      end

      /*************************************************************************
      * Channel request state machine
      *************************************************************************/
      /* registered hrdata */
      if(hready_lli)
      begin
        htrans_lli_1t <= htrans_lli[1];
        if(htrans_lli_1t)
          hrdata_lli_1t <= hrdata_lli;
      end
      
      /* FSM */
      case(request_state)
        /***********************************************************************
        * IDLE: wait any incoming channel request
        ***********************************************************************/
        S_IDLE:
        begin
          if(oft_free!=16'b0 && arb_valid==1'b1)
          begin
            lli_channel        <= arb_channel;
            lli_pri_level      <= arb_level;                 
            channel_tag        <= oft_free_entry;        
            haddr_lli          <= ch_lli_root[arb_channel];
            htrans_lli         <= 2'b10;                 
            request_state      <= S_LLI_ADDR;
          end            
        end
        /***********************************************************************
        * LLI_ADDR: wait acquistion of the burst first address
        ***********************************************************************/
        S_LLI_ADDR:
        begin
          if(hready_lli==1)
          begin
            htrans_lli    <= 2'b11;
            request_state <= S_LLI_D0;
          end
        end
       
        /***********************************************************************
        * LLI_D0: acquisition of the source address parameter
        ***********************************************************************/
        S_LLI_D0:
        begin
          if(hready_lli==1)
            request_state <= S_LLI_D1;
        end
       
        /***********************************************************************
        * LLI_D1: acquisition of the destination address parameter
        ***********************************************************************/
        S_LLI_D1:
        begin
          channel_saddr          <= hrdata_lli_1t;
          oft_saddr[channel_tag] <= hrdata_lli_1t[31:0];
          if(hready_lli==1)
            request_state <= S_LLI_D2;
        end

        /***********************************************************************
        * LLI_D2: acquisition of the length parameter, lli irqs and counters
        ***********************************************************************/
        S_LLI_D2:
        begin
          channel_daddr          <= hrdata_lli_1t;
          oft_daddr[channel_tag] <= hrdata_lli_1t;
          if(hready_lli==1)
          begin
            htrans_lli     <= 2'b00;
            request_state  <= S_LLI_D3;
          end
        end

        /***********************************************************************
        * LLI_D3: acquisition of the next LLI pointer
        ***********************************************************************/
        S_LLI_D3:
        begin
          oft_lli_counter_en[channel_tag] <= hrdata_lli_1t[20];     
          oft_lli_counter_no[channel_tag] <= hrdata_lli_1t[19:16]; 
          //--add by fengmaoqiao
          channel_if_add_data             <= hrdata_lli_1t[31:29]; 
          //--edit--
          oft_lli_irq_en[channel_tag]     <= hrdata_lli_1t[28];     
          oft_lli_irq_no[channel_tag]     <= hrdata_lli_1t[27:24];  
          /* bytes quantity of the payload */
          oft_length[channel_tag]         <= hrdata_lli_1t[15:0];                   
          channel_length                  <= hrdata_lli_1t[15:0];     
          if(hready_lli==1)
            request_state <= S_REQUEST;
        end  
        
        /***********************************************************************
        * REQUEST: generate request to physical channel
        ***********************************************************************/
        S_REQUEST:
        begin
          if(hrdata_lli_1t==32'b0 && ch_mutex[lli_channel]==1'b1)
          begin                                                                           
            /* the next pointer of the descriptor is null and the 
               spinlock has been set by the software, meaning that the
               software is working on this descriptor, then the 
               current descriptor request is canceled */ 
            ch_stopped[lli_channel] <= 1'b1;                                                          
            request_state           <= S_IDLE;                                                      
                                                                                          
          end                                                                             
          else                                                                            
          begin                                                                           
            /* allocate entry within the outstanding fragment table */                    
            oft_free[channel_tag]         <= 1'b0;                                        
            /* increment downstream_tag_taken counter */
            if(lli_channel[1]==1'b1)
              downstream_tag_taken <= downstream_tag_taken + 4'd1;
            /* update the lli pointer */                                                  
            ch_lli_root[lli_channel]       <= hrdata_lli_1t;                               
            /* if pointer is null, then signal end of fragment interrupt */               
            if(hrdata_lli_1t==32'b0)                                                      
            begin                                                                         
               oft_eof_irq_en[channel_tag] <= 1'b1;                                       
               oft_eof_irq_no[channel_tag] <= lli_channel;                                      
            end                                                                           
            else                                                                          
            begin
               oft_eof_irq_en[channel_tag] <= 1'b0;                                       
            end
                                                                                          
            /* send the request */                                                        
            channel_req                   <= 1'b1;                                        
            channel_dir                   <= lli_channel[1];                                        
            /* move served channel to lowest priority */
            case(lli_pri_level)
              2'd0:   {arb_q0,arb_q1,arb_q2,arb_q3} <= {arb_q1,arb_q2,arb_q3,arb_q0};
              2'd1:   {arb_q0,arb_q1,arb_q2,arb_q3} <= {arb_q0,arb_q2,arb_q3,arb_q1};
              2'd2:   {arb_q0,arb_q1,arb_q2,arb_q3} <= {arb_q0,arb_q1,arb_q3,arb_q2};
              default:{arb_q0,arb_q1,arb_q2,arb_q3} <= {arb_q0,arb_q1,arb_q2,arb_q3};
            endcase
            /* move to S_ACCEPT state, ensure that phy channel has accepted the req */
            request_state <= S_ACCEPT;                                                    
          end                                                                             
        end
        
        /***********************************************************************
        * ACCEPT: ensure that the physical channel has accepted the request
        ***********************************************************************/
        default:
        begin
          if(~channel_dir & upstream_busy |
              channel_dir & downstream_busy)
          begin
            channel_req   <= 1'b0;
            request_state <= S_IDLE;
          end
        end
      endcase
      
      /*************************************************************************
      * AHB address incrementation
      *************************************************************************/
      if(hready_lli && 
         (request_state==S_LLI_ADDR || 
          request_state==S_LLI_D0   || 
          request_state==S_LLI_D1))
          haddr_lli <= haddr_lli + 4;
    
    end
    
  end
  
  /*****************************************************************************
  * Debug instrumentation
  *****************************************************************************/
  `ifdef RW_SIMU
  
    /* display string with an ascii form */
    reg [16*8-1:0] request_state_str;
    always @(*)
    
      case (request_state)
      
        S_IDLE:     request_state_str = "S_IDLE";
        S_LLI_ADDR: request_state_str = "S_LLI_ADDR";
        S_LLI_D0:   request_state_str = "S_LLI_D0";   
        S_LLI_D1:   request_state_str = "S_LLI_D1"; 
        S_LLI_D2:   request_state_str = "S_LLI_D2";
        S_LLI_D3:   request_state_str = "S_LLI_D3";
        S_REQUEST:  request_state_str = "S_REQUEST";
        S_ACCEPT:   request_state_str = "S_ACCEPT";
        default:    request_state_str = "UNDEF";
      endcase
      
     reg [4:0] oft_free_dbg;
    
     always @(*)
     begin:b_debug_free_entry
     
       integer v_i;
       
       oft_free_dbg=0;
       for(v_i=0;v_i<16;v_i=v_i+1) 
       
         if(oft_free[v_i]) oft_free_dbg =  oft_free_dbg + 1;  

     end

  `endif
  
endmodule
