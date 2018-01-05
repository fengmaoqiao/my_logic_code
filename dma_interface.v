
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
module dma_interface(
        //clock and reset        
        input                       clk                         ,
        input                       rst_n                       ,
        
        //Dinidma bus interface
        //upstream interface

        output  reg [63:0]              dma0_fromhost_data          ,
        
        output  reg [ 7:0]              dma0_fromhost_ctrl          ,
        
        output  reg                     dma0_fromhost_valid         ,
        
        input                           dma0_fromhost_accept        ,

        
        input   [63:0]                  dma0_tohost_data            ,
        
        input   [ 7:0]                  dma0_tohost_ctrl            ,
        
        input                           dma0_tohost_valid           ,
        
        output  wire                    dma0_tohost_almost_full      ,
        //downstream interface 
        //Data and Ack backward to underlayer
        
        output  wire [63:0]             dma1_fromhost_data          ,
        
        output  wire [7:0]              dma1_fromhost_ctrl          ,
        
        output  wire                    dma1_fromhost_valid         ,
        
        input                           dma1_fromhost_accept        ,

        //Req forward to this module
        input       [63:0]              dma1_tohost_data            ,
        
        input       [ 7:0]              dma1_tohost_ctrl            ,
        
        input                           dma1_tohost_valid           ,
        
        output  reg                     dma1_tohost_almost_full      ,
        
        //axi stream bus interface
        //upstream
        input                           s0_axis_fromhost_tvalid         ,
        
        output reg                      s0_axis_fromhost_tready         ,
        
        input  [63:0]                   s0_axis_fromhost_tdata          ,
        
        input  [7:0]                    s0_axis_fromhost_tkeep          ,
        
        input                           s0_axis_fromhost_tlast          ,
        
                 
        output wire                     m0_axis_tohost_tvalid          ,
        
        input                           m0_axis_tohost_tready          ,
        
        output wire [63:0]              m0_axis_tohost_tdata           ,
        
        output wire [7:0]               m0_axis_tohost_tkeep           ,
        
        output                          m0_axis_tohost_tlast           ,
        //downstream 
        //Fifo write to DMA Interface channel ,for data
        
        input                           s1_axis_fromhost_tvalid   ,
        
        output wire                     s1_axis_fromhost_tready   ,  //DMA Interface can receive data?
        
        input     [63:0]                s1_axis_fromhost_tdata    ,
        
        input     [7:0]                 s1_axis_fromhost_tkeep    ,
                       
        input                           s1_axis_fromhost_tlast    ,  //the tranfer end
        
        
        output reg                      m1_axis_tohost_tvalid     ,
        
        input                           m1_axis_tohost_tready     ,
        
        output reg [63:0]               m1_axis_tohost_tdata      ,
        
        output reg [7:0]                m1_axis_tohost_tkeep      ,
        
        output reg                      m1_axis_tohost_tlast      
      
                                        
        
        
        );
        
        //  --------------------------------------------------------------------------------
      (* syn_keep="true" *)reg           state_data;
      (* syn_keep="true" *)reg [63:0]    dma1_fromhost_data_temp;
      (* syn_keep="true" *)reg           dma1_fromhost_valid_temp;      
      (* syn_keep="true" *)reg [7:0]     dma1_fromhost_ctrl_temp;
                        
      (* syn_keep="true" *)wire [7:0]    dma1_fromhost_ctrl_end;
      
      (* syn_keep="true" *)assign        dma1_fromhost_data      =       state_data ? s1_axis_fromhost_tdata   : dma1_fromhost_data_temp;
      (* syn_keep="true" *)assign        dma1_fromhost_valid     =       state_data ? s1_axis_fromhost_tvalid  : dma1_fromhost_valid_temp;    
      (* syn_keep="true" *)assign        s1_axis_fromhost_tready =       state_data ? dma1_fromhost_accept  : 1'b0;      
      (* syn_keep="true" *)assign        dma1_fromhost_ctrl      =       (s1_axis_fromhost_tlast && s1_axis_fromhost_tready && s1_axis_fromhost_tvalid) ? 
        (dma1_fromhost_ctrl_end)
      : (dma1_fromhost_ctrl_temp);
      
         // (dma1_fromhost_ctrl_end & {8{dma1_fromhost_accept}} & {8{dma1_fromhost_valid}}) 
       // : (dma1_fromhost_ctrl_temp & {8{dma1_fromhost_accept}} & {8{dma1_fromhost_valid_temp}});
             
      (* syn_keep="true" *)assign        dma1_fromhost_ctrl_end = (s1_axis_fromhost_tkeep <=8'b00001111) ? 8'b00010100 : 8'b00011100; 
     
      reg           req_data_switch;
     
      reg [63:0]    dma0_tohost_data_temp;
     
      reg           dma0_tohost_valid_temp;
      
      
      reg [31:0] up_tag_num;
      reg [15:0] up_data_length;
      reg [15:0] count;
      
      (* syn_keep="true" *)assign        m0_axis_tohost_tdata      =         req_data_switch ? dma0_tohost_data      : dma0_tohost_data_temp;
      (* syn_keep="true" *)assign        m0_axis_tohost_tvalid     =         req_data_switch ? dma0_tohost_valid     : dma0_tohost_valid_temp;
      (* syn_keep="true" *)assign        m0_axis_tohost_tkeep      =         (dma0_tohost_ctrl[3] == 1'b1 && up_data_length[0] == 1'b1) ? 8'b0000_1111 : 8'b1111_1111;  
      (* syn_keep="true" *)assign        dma0_tohost_almost_full   =         req_data_switch ? (~m0_axis_tohost_tready) : 1'b0; 


      
      wire channel_if_add_data;
      assign channel_if_add_data = 1'b0;
      
                        
  // -----------------------------------------------------------------------------
//**********************************************************
//Signal Declation
//**********************************************************
  localparam DOWN_IDLE = 3'd0;
  localparam DOWN_ACK_1 = 3'd1;
  localparam DOWN_ACK_2 = 3'd2;
  localparam DOWN_DATA = 3'd3;
  
  localparam UP_IDLE = 3'd0;
  localparam UP_DATA = 3'd1;
  localparam UP_REQ2 = 3'd2;
  localparam UP_ACK_1 = 3'd3;
  localparam UP_ACK_2 = 3'd4;
  localparam UP_DATA_END = 3'd5;
  
  localparam S_UPSTREAM = 3'd0;
  localparam S_DOWNSREAM = 3'd1;
  
  reg [3:0]  tag_num;
  reg [15:0] cnt_tohost_data;
  reg [15:0] length_transfer_words;
  
  
  reg [3:0] down_state;
  
  reg[3:0] up_state;
  
  wire  fifo_full;
  reg [63:0] fifo_din;
  reg   fifo_wr_en;
  
  wire  fifo_empty;
  wire [63:0] fifo_dout;
  reg   fifo_rd_en;
  
  wire [5:0] write_count;
  wire [5:0] read_count;
  
  
  reg  [63:0] current_req;
  wire  [15:0] current_length_int;
  
  
  reg  [31:0] current_length;
  reg  [2:0]  down_dst_addr;
  reg  [2:0]  up_src_addr;
  

  
  
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
 
  always@(posedge clk,negedge rst_n)
  begin 
   if(!rst_n)
   begin
    //s1_axis_fromhost_tready  <= 1'b0;
    dma1_tohost_almost_full      <= 1'b0;
    dma1_fromhost_ctrl_temp     <= 8'b0;
    cnt_tohost_data             <= 16'd0;
    length_transfer_words       <= 16'd0;
    fifo_wr_en                  <= 1'b0;
    down_state                  <= DOWN_IDLE;
    down_dst_addr               <= 3'b0;
    
    state_data                  <= 1'b0;  //--edit
   end
   else
   begin
    //If the Req is the first Req word,so save the Req information to fifo.
    if(dma1_tohost_ctrl[4] & ~dma1_tohost_ctrl[3] & dma1_tohost_valid)
    begin 
     if(!fifo_full)
     begin
      
      fifo_wr_en                <= 1'b1;
      fifo_din                  <= dma1_tohost_data;
      dma1_tohost_almost_full    <= 1'b0;
      
     end
     
     else
      begin
      
       fifo_wr_en               <= 1'b0;
       dma1_tohost_almost_full   <= 1'b1;
      
      end
    end
    else
     fifo_wr_en   <= 1'b0;
    
     
     
    case(down_state)
    //If the fifo not empty,read the req from it
    DOWN_IDLE:begin
    
     cnt_tohost_data        <= 0;  
     // --edit       
     dma1_fromhost_data_temp[63:0]  <= 64'b1;
     dma1_fromhost_valid_temp       <= 1'b0;   //downstream stop
     dma1_fromhost_ctrl_temp        <=8'b0;
     
     if(!fifo_empty)
     begin
     
      fifo_rd_en                 <= 1'b1;     //read the first req
      current_req                <= fifo_dout;
      down_state                 <= DOWN_ACK_1;
      
      tag_num                    <= fifo_dout[39:36];
      length_transfer_words      <= fifo_dout[15:0]; 
      down_dst_addr              <= fifo_dout[29:27];
                       
     end
     else
      begin
      
       down_state    <= DOWN_IDLE;
       fifo_rd_en    <= 1'b0;
       
      end
    end
    //Return Ack to DMA InterFace
    DOWN_ACK_1:
    begin
     fifo_rd_en   <= 1'b0;
     
     if(dma1_fromhost_accept && dma1_fromhost_valid_temp)
     begin
     
      dma1_fromhost_valid_temp   <= 1'b1;
      
      dma1_fromhost_ctrl_temp[0]  <= 1'b1;   //thit is first ack
      dma1_fromhost_ctrl_temp[2]  <= 1'b0;   //data valid
      dma1_fromhost_ctrl_temp[3]  <= 1'b0;   //data valid
      dma1_fromhost_ctrl_temp[4]  <= 1'b0;   //this is down stream ack
      dma1_fromhost_ctrl_temp[5]  <= 1'b0;  
      
      dma1_fromhost_data_temp[7:4]  <= tag_num;
      down_state                    <= DOWN_ACK_2;
      
     end
     else begin
     
      dma1_fromhost_valid_temp      <= 1'b1;
      down_state                    <= DOWN_ACK_1;
      
      end
    end
    
    DOWN_ACK_2:
    begin
     if(dma1_fromhost_accept)
     begin
     
      dma1_fromhost_valid_temp          <= 1'b1;
      dma1_fromhost_data_temp[15:0]     <= length_transfer_words;
      dma1_fromhost_data_temp[23:16]    <= 8'd0;
      
      dma1_fromhost_ctrl_temp[0]   <= 1'b0;   //thit is second ack
      dma1_fromhost_ctrl_temp[2]   <= 1'b0;   //data valid
      dma1_fromhost_ctrl_temp[3]   <= 1'b0;   //data valid
      dma1_fromhost_ctrl_temp[4]   <= 1'b0;   //this is down stream ack
      dma1_fromhost_ctrl_temp[5]   <= 1'b1;        
                    
      down_state      <= DOWN_DATA;
            
     end
     else 
      begin
      
      dma1_fromhost_valid_temp      <= 1'b1;
      down_state                    <= DOWN_ACK_2;
      
      end
    end
    
    //When finish Ack,ready to transfer data
    DOWN_DATA:
    begin
        state_data      <=  1'b1;
          //If Dinidma is ready to get data
     if(dma1_fromhost_accept )
     begin
            
        dma1_fromhost_ctrl_temp[0]  <= 1'b0;   //thit is data
        dma1_fromhost_ctrl_temp[2]  <= 1'b1;   //lower data valid
        dma1_fromhost_ctrl_temp[3]  <= 1'b1;   //upper data invalid   --
        dma1_fromhost_ctrl_temp[4]  <= 1'b0;   //this is down stream ack
        dma1_fromhost_ctrl_temp[5]  <= 1'b0;   
            
      if((s1_axis_fromhost_tvalid == 1'b1)&&(s1_axis_fromhost_tready == 1'b1))
      begin
      
        cnt_tohost_data   <= cnt_tohost_data + 1;
             
      end
     end
     else
     begin
                 
        down_state     <= DOWN_DATA;
      
     end
     
     if( (s1_axis_fromhost_tlast == 1'b1) && (s1_axis_fromhost_tready == 1'b1))
     begin
     
        cnt_tohost_data     <= 16'd0;      
        down_state     <= DOWN_IDLE;            
        state_data     <= 1'b0;   
        dma1_fromhost_valid_temp       <= 1'b0;   //downstream stop
        dma1_fromhost_ctrl_temp        <=8'b0;
           
     end 

                   
    end
   endcase
  end
 end
 
assign m0_axis_tohost_tlast = (dma0_tohost_ctrl[3] == 1'b1) && (up_state == UP_DATA);
 //   --      Upstream process      --    //
 always@(posedge clk or negedge rst_n)
 begin
  if(!rst_n)
  begin
     
   dma0_fromhost_ctrl           <= 8'b0;                 //to dinidma  
   dma0_fromhost_data           <= 64'b0;  
   dma0_fromhost_valid          <= 1'b0;
   
   dma0_tohost_data_temp        <= 64'b0;
   dma0_tohost_valid_temp       <= 1'b0;
                              
   up_state                     <= UP_IDLE;
   req_data_switch              <= 1'b0;                // use temp
   
   up_src_addr                  <= 3'b0;
  
  end
  else
   casez(up_state)
   UP_IDLE:
   begin

    dma0_fromhost_valid             <= 1'b0;         
    
    // if req come,save the information and jump to req2
    if(dma0_tohost_ctrl[4] & ~dma0_tohost_ctrl[3] & dma0_tohost_valid & m0_axis_tohost_tready)      
    begin
    
      up_state                      <= UP_REQ2;      
      up_tag_num                    <= dma0_tohost_data[63:32];       //save tag number
      up_data_length[15:0]          <= dma0_tohost_data[15:0];      //save data length
      up_src_addr                   <= dma0_tohost_data[29:27];
      
    end
    else
    
      up_state                      <= UP_IDLE;
      
   end
   
   //REQ2 is the host information ,no use
    UP_REQ2:
     begin
        if(dma0_tohost_ctrl[4] & ~dma0_tohost_ctrl[3] & dma0_tohost_valid & m0_axis_tohost_tready)
        begin
        
            up_state                <= UP_DATA;            
            req_data_switch         <= 1'b1;
            
        end
        else
        
        up_state                    <= UP_REQ2;
         
     end

   
    UP_DATA:
     begin

        if(dma0_tohost_ctrl[3] == 1'b1)
        begin
        
          up_state                <= UP_ACK_1;
          req_data_switch         <= 1'b0;                      //switch    
                      
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
            
            dma0_fromhost_ctrl[0]   <= 1'b1;                     //first ack
            dma0_fromhost_ctrl[4]   <= 1'b1;                     //
            dma0_fromhost_ctrl[5]   <= 1'b0;                     //second ack
            
            dma0_fromhost_data[7:4] <= up_tag_num[7:4];         //send tag number 
            
            up_state                         <= UP_ACK_2;

     end
      
      
     UP_ACK_2:
      begin
             dma0_fromhost_valid     <= 1'b1;
             
             dma0_fromhost_ctrl[0]  <= 1'b0;                     //first ack
             dma0_fromhost_ctrl[4]  <= 1'b1;                     //
             dma0_fromhost_ctrl[5]  <= 1'b1;                     //second ack
             
             dma0_fromhost_data[23:0] <= up_data_length;         //send data length
             
             up_state                         <= UP_IDLE;

      end

   default: up_state     <= UP_IDLE;
  endcase
 end
 

 
 

endmodule

