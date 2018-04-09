//**********************************************************
//
// Copyright(c) 2017 . Outwitcom Technology Co., LTD.
// All rights reserved.
//
// ProjectName :
// target      :
// FileName    : dma_interface.sv
// Author      : fengmaoqiao
// E_mail      : fengmaoqiao@outwitcom.com
// Date        :
// Version     :
//
// Modification history
//--------------------------------------------------------
// $Log:$
//
//
//**********************************************************
`default_nettype wire
`define simu_on 0

module dma_interface(
  //clock and reset        
  input                       clk                         ,
  input                       rst_n                       ,
  
  /***********************************************************
  * Upstream channel associate with DiniDMA 
  ***********************************************************/
  output  reg [63:0]              dma0_fromhost_data          ,
  output  reg [ 7:0]              dma0_fromhost_ctrl          ,
  output  reg                     dma0_fromhost_valid         ,
  input                           dma0_fromhost_accept        ,
  
  input   [63:0]                  dma0_tohost_data            ,
  input   [ 7:0]                  dma0_tohost_ctrl            ,
  input                           dma0_tohost_valid           ,
  output  wire                    dma0_tohost_almost_full     ,
  /***********************************************************
  * Downstream channel associate with DiniDMA
  ***********************************************************/
  output  wire [63:0]             dma1_fromhost_data          ,
  output  wire [7:0]              dma1_fromhost_ctrl          ,
  output  wire                    dma1_fromhost_valid         ,
  input                           dma1_fromhost_accept        ,

  input       [63:0]              dma1_tohost_data            ,
  input       [ 7:0]              dma1_tohost_ctrl            ,
  input                           dma1_tohost_valid           ,
  output  reg                     dma1_tohost_almost_full     ,
 
  /***********************************************************
  * Upstream axi stream fifo Interface
  ***********************************************************/
  input                           s0_axis_fromhost_tvalid     ,
  output reg                      s0_axis_fromhost_tready     ,
  input  [63:0]                   s0_axis_fromhost_tdata      ,
  input  [7:0]                    s0_axis_fromhost_tkeep      ,
  input                           s0_axis_fromhost_tlast      ,
  
  output wire                     m0_axis_tohost_tvalid       ,
  input                           m0_axis_tohost_tready       ,
  output wire [63:0]              m0_axis_tohost_tdata        ,
  output reg  [7:0]               m0_axis_tohost_tkeep        ,
  output                          m0_axis_tohost_tlast        ,
  /***********************************************************
  * Downstream axi stream fifo Interface 
  ***********************************************************/
  input                           s1_axis_fromhost_tvalid     ,
  output wire                     s1_axis_fromhost_tready     ,  
  input     [63:0]                s1_axis_fromhost_tdata      ,
  input     [7:0]                 s1_axis_fromhost_tkeep      ,
  input                           s1_axis_fromhost_tlast      ,  
  
  output reg                      m1_axis_tohost_tvalid       ,
  input                           m1_axis_tohost_tready       ,
  output reg [63:0]               m1_axis_tohost_tdata        ,
  output reg [7:0]                m1_axis_tohost_tkeep        ,
  output reg                      m1_axis_tohost_tlast      
        
        );
        
  /**********************************************************
  * FSM state Declation
  **********************************************************/
  localparam  DOWN_IDLE     = 4'd1,
              DOWN_ACK_1    = 4'd2,
              DOWN_ACK_2    = 4'd4,
              DOWN_DATA     = 4'd8;
  
  localparam  UP_IDLE       = 8'd1,
              UP_DATA       = 8'd2,
              UP_REQ2       = 8'd4,
              UP_ACK_1      = 8'd8,
              UP_ACK_2      = 8'd16,
              UP_DATA_END   = 8'd32;
  
  localparam  S_UPSTREAM    = 2'd0,
              S_DOWNSREAM   = 2'd1;
  

  /***********************************************************
  * Signal Declation
  ***********************************************************/
  reg           state_data;
  reg  [63:0]   dma1_fromhost_data_temp;
  reg           dma1_fromhost_valid_temp;      
  reg  [7:0]    dma1_fromhost_ctrl_temp;
  wire [7:0]    dma1_fromhost_ctrl_end;
             
  reg           req_data_switch;
  reg  [63:0]   dma0_tohost_data_temp;
  reg           dma0_tohost_valid_temp;
      
  reg  [31:0]   up_tag_num;
  reg  [15:0]   up_data_length;
  reg  [15:0]   count;
      
  reg  [3:0]    tag_num;
  reg  [15:0]   cnt_tohost_data;
  reg  [15:0]   length_transfer_words;
  //the bytes length in this transfer,from req
  reg  [15:0]   bytes_transfer;
  
  reg  [7:0]    down_state; 
  reg  [7:0]    up_state;
  
  reg  [63:0]   current_req;
  wire [15:0]   current_length_int;
  
  reg  [31:0]   current_length;
  reg  [2:0]    down_dst_addr;
  reg  [2:0]    up_src_addr;

  wire          down_last_be;
  /***********************************************************
  * Signal for the FIFO
  ***********************************************************/
  wire          fifo_full;
  reg [63:0]    fifo_din;
  reg           fifo_wr_en;
  
  wire          fifo_empty;
  wire [63:0]   fifo_dout;
  reg           fifo_rd_en;
  
  wire [5:0]    write_count;
  wire [5:0]    read_count;
  /***********************************************************
  * Assign combinatory logic
  ***********************************************************/
  /*  Downstream Channel  */
  assign   down_last_be               =       s1_axis_fromhost_tlast & s1_axis_fromhost_tready & s1_axis_fromhost_tvalid;
  assign   dma1_fromhost_ctrl_end     =       (s1_axis_fromhost_tkeep <=8'b00001111) ? 8'b00010100 : 8'b00011100;
  /*  Upstream Channel */
  assign   m0_axis_tohost_tdata       =       req_data_switch ? dma0_tohost_data      : dma0_tohost_data_temp;
  assign   m0_axis_tohost_tvalid      =       req_data_switch ? dma0_tohost_valid     : dma0_tohost_valid_temp;
  assign   dma0_tohost_almost_full    =       req_data_switch ? (~m0_axis_tohost_tready) : 1'b0; 
      
  /***********************************************************
  * Use a fifo to story the Req signal from DiniDMA 
  ***********************************************************/
  fifo_generator_0 fifo_generator_0_i(
  .wr_clk(clk),
  .rd_clk(clk),
  .rst(~rst_n),
  .full(fifo_full),
  .din(fifo_din),
  .wr_en(fifo_wr_en),
  .empty(fifo_empty),
  .dout(fifo_dout),
  .rd_en(fifo_rd_en),
  .rd_data_count(read_count),
  .wr_data_count(write_count)
  );
 
  /***********************************************************
  * Main Logic 
  ***********************************************************/
  always @(posedge clk or negedge rst_n)begin
  if(!rst_n)
      current_state <= IDLE;
    end
    else begin
      current_state <= next_state;
    end
  end


  always @(*)begin
    case(current_state)
      IDLE:
        if(!fifo_empty)
          next_state = DOWN_ACK_1;
        else
          next_state = IDLE;
    
      DOWN_ACK_1:
        if(dma1_fromhost_accept && dma1_fromhost_valid_temp)
          next_state = DOWN_ACK_2;
        else
          next_state = DOWN_ACK_1;

      DOWN_ACK_2:
        if(dma1_fromhost_accept)
          next_state = DOWN_DATA;
        else
          next_state = DOWN_ACK_2;

      DOWN_DATA:
        if(s1_axis_fromhost_tlast == 1'b1 && s1_axis_fromhost_tready == 1'b1)
          next_state = DOWN_IDLE;
        else
          ;
      default : next_state=IDLE;
        end
    endcase
  end

  localparam  WD_TIME_OVER 30000
  reg [31:0]  wd_timer;
  reg         time_out;    
  always @(posedge clk or negedge rst_n)
  begin
    if(!rst_n)begin
      wd_timer <= 32'd0;
      time_out <= 1'b0;
    end
    else
      if(wd_timer == WD_TIME_OVER)
      begin
         wd_timer <= 32'b0;
         time_out <= 1'b1;
      end
      else
         wd_timer <= wd_timer + 1;
    end
  end




  always @(*)
  begin
    case(current_state):
      DOWN_IDLE:begin
        /* Initial */
        cnt_tohost_data                 = 0;
        dma1_fromhost_data_temp         = 64'b1;

        dma1_fromhost_valid_temp        = 1'b0;
        dma1_fromhost_ctrl_temp         = 8'b0;

        state_data                      = 1'b0;

        /* Get the REQ from fifo */
        if(~fifo_empty)
        begin

          fifo_rd_en                    = 1'b1;
          current_req                   = fifo_dout;
          tag_num                       = fifo_dout[39:36];
          length_transfer_words         = fifo_dout[15:0];
          down_dst_addr                 = fifo_dout[29:27];
        end
      end
      /* Return the first ACK to Dinidma */
      DOWN_ACK_1:begin
        dma1_fromhost_valid_temp        = 1'b1;

        dma1_fromhost_ctrl_temp[0]      = 1'b1;
        dma1_fromhost_ctrl_temp[2]      = 1'b0;
        dma1_fromhost_ctrl_temp[3]      = 1'b0;
        dma1_fromhost_ctrl_temp[4]      = 1'b0;
        dma1_fromhost_ctrl_temp[5]      = 1'b0;

        dma1_fromhost_ctrl_temp[7:4]    = tag_num;
      end
      /* Return the second ACK to Dinidma */
      DOWN_ACK_2:begin
        dma1_fromhost_valid_temp        = 1'b1;
        dma1_fromhost_data_temp[15:0]   = length_transfer_words;
        dma1_fromhost_data_temp[23:16]  = 8'd0;

        dma1_fromhost_ctrl_temp[0]      = 1'b0;
        dma1_fromhost_ctrl_temp[2]      = 1'b0;
        dma1_fromhost_ctrl_temp[3]      = 1'b0;
        dma1_fromhost_ctrl_temp[4]      = 1'b0;
        dma1_fromhost_ctrl_temp[5]      = 1'b1;
      end
      
      /* Trans the DATA to Dinidma */
      DOWN_DATA:begin
        state_data                      = 1'b1;

        dma1_fromhost_ctrl_temp[0]      = 1'b0;
        dma1_fromhost_ctrl_temp[2]      = 1'b1;
        dma1_fromhost_ctrl_temp[3]      = 1'b1;
        dma1_fromhost_ctrl_temp[4]      = 1'b0;
        dma1_fromhost_ctrl_temp[5]      = 1'b0;

        dma1_fromhost_data              = s1_axis_fromhost_tdata;
        dma1_fromhost_tvalid            = s1_axis_fromhost_tvalid;

        s1_axis_fromhost_tready         = dma1_fromhost_accept;

        if(down_last_be)
          dma1_fromhost_ctrl = dma1_fromhost_ctrl_end;
        else
          dma1_fromhost_ctrl = dma1_fromhost_ctrl_temp;

      end
  end

  assign m0_axis_tohost_tlast = (dma0_tohost_ctrl[3] == 1'b1) && (up_state == UP_DATA);
  /***********************************************************
  * Upstream Channel Transfer
  ***********************************************************/
  always@(posedge clk or negedge rst_n)
  begin
  if(!rst_n)
  begin
     
   dma0_fromhost_ctrl           <= 8'b0;                          //to dinidma  
   dma0_fromhost_data           <= 64'b0;  
   dma0_fromhost_valid          <= 1'b0;
   
   dma0_tohost_data_temp        <= 64'b0;
   dma0_tohost_valid_temp       <= 1'b0;
                              
   up_state                     <= UP_IDLE;
   req_data_switch              <= 1'b0;                          // use temp
   
   up_src_addr                  <= 3'b0;
  
  end
  else
   casez(up_state)
   UP_IDLE:
   begin

    dma0_fromhost_valid             <= 1'b0;         
    
    /* if req come,save the information and jump to req2 */
    if(dma0_tohost_ctrl[4] & ~dma0_tohost_ctrl[3] & dma0_tohost_valid & m0_axis_tohost_tready)      
    begin
    
      up_state                      <= UP_REQ2;      
      up_tag_num                    <= dma0_tohost_data[63:32];       //save tag number
      up_data_length[15:0]          <= dma0_tohost_data[15:0];        //save data length
      up_src_addr                   <= dma0_tohost_data[29:27];
      
    end
    else
    
      up_state                      <= UP_IDLE;
      
   end
   
   /* REQ2 is the host information ,no use */
    UP_REQ2:
     begin
        if(dma0_tohost_ctrl[4] & ~dma0_tohost_ctrl[3] & dma0_tohost_valid & m0_axis_tohost_tready)
        begin
        
            up_state                <= UP_DATA;            
            req_data_switch         <= 1'b1;
            bytes_transfer          <= dma0_tohost_data[63:48];
        end
        else
        
        up_state                    <= UP_REQ2;
         
     end

   
    UP_DATA:
     begin

        if(dma0_tohost_ctrl[3] == 1'b1)
        begin
        
          up_state                <= UP_ACK_1;
          req_data_switch         <= 1'b0;                              //switch    
                      
        end
        else
        begin
        
          up_state                <= UP_DATA;            
          count                   <= count + 1;
          
        end
      end
   
    UP_ACK_1:
     begin            
            dma0_fromhost_valid     <= 1'b1;
            
            dma0_fromhost_ctrl[0]   <= 1'b1;                            //first ack
            dma0_fromhost_ctrl[4]   <= 1'b1;                            //
            dma0_fromhost_ctrl[5]   <= 1'b0;                            //second ack
            
            dma0_fromhost_data[7:4] <= up_tag_num[7:4];                 //send tag number 
            
            up_state                         <= UP_ACK_2;

     end
      
      
     UP_ACK_2:
      begin
             dma0_fromhost_valid     <= 1'b1;
             
             dma0_fromhost_ctrl[0]  <= 1'b0;                            //first ack
             dma0_fromhost_ctrl[4]  <= 1'b1;                            //
             dma0_fromhost_ctrl[5]  <= 1'b1;                            //second ack
             
             dma0_fromhost_data[23:0] <= up_data_length[15:0];          //send data length
             up_state                         <= UP_IDLE;

           end

   default: up_state     <= UP_IDLE;
  endcase
 end
 
  /***********************************************************
  * The last transfer bytes , must write to AXI FIFO to
  * make sure the numbers of transfer right.
  ***********************************************************/
always @(*)begin
    if(dma0_tohost_ctrl[3])
    begin
        case(bytes_transfer[2:0]):
            3'b000:m0_axis_tohost_tkeep = 8'b1111_1111;
            3'b001:m0_axis_tohost_tkeep = 8'b0000_0001;
            3'b010:m0_axis_tohost_tkeep = 8'b0000_0011;
            3'b011:m0_axis_tohost_tkeep = 8'b0000_0111;

            3'b100:m0_axis_tohost_tkeep = 8'b0000_1111;
            3'b101:m0_axis_tohost_tkeep = 8'b0001_1111;
            3'b110:m0_axis_tohost_tkeep = 8'b0011_1111;
            3'b111:m0_axis_tohost_tkeep = 8'b0111_1111;
            default: m0_axis_tohost_tkeep = 8'b1111_1111;
          endcase
        end
    else
        m0_axis_tohost_tkeep = 8'b1111_1111;
end

  /***********************************************************
  * For Simulate,Change the FSM code to ASCII
  ***********************************************************/
`ifdef simu_on
  reg [15*8:0] down_state_str;
  reg [15*8:0] up_state_str;   

always @(*)begin
  case(down_state)
        DOWN_IDLE   :   down_state_str  = {"IDLE"};
        DOWN_ACK_1  :   down_state_str  = {"DOWN_ACK_1"};
        DOWN_ACK_2  :   down_state_str  = {"DOWN_ACK_2"};
        DOWN_DATA   :   down_state_str  = {"DOWN_DATA"};
        default     :   down_state_str  = {"xxx"};
  endcase
end

always @(*)begin
  case(up_state)
        UP_IDLE     :   up_state_str    = {"UP_IDLE"};
        UP_REQ2     :   up_state_str    = {"UP_REQ2"};
        UP_ACK_1    :   up_state_str    = {"UP_ACK_1"};
        UP_ACK_2    :   up_state_str    = {"UP_ACK_2"};
        UP_DATA     :   up_state_str    = {"UP_DATA"};
        UP_DATA_END :   up_state_str    = {"UP_DATA_END"};
        default     :   up_state_str    = {"xxx"};
  endcase
end
`endif
endmodule

