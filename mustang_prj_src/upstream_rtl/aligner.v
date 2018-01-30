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
// Description      : upstream aligner module
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

module down_aligner
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire           clk,
  input  wire           rst_n,

  /*****************************************************************************
  * 
  *****************************************************************************/
  input  wire           start,
  input  wire  [2:0]    src_addr,
  input  wire  [2:0]    dst_addr,

  /*****************************************************************************
  * 
  *****************************************************************************/
  input  wire [63:0]    datai,
  input  wire           datai_en,
  input  wire           datai_last,

  /*****************************************************************************
  * 
  *****************************************************************************/
  output wire [63:0]    datao,
  output wire           datao_en
);

  /*****************************************************************************
  * declarations
  *****************************************************************************/
  /* wires */
  reg [63:0] data_rot;
  
  /* flops */
  reg [ 2:0] align_rot;
  reg [63:0] align_mask;
  reg        first_is_merged;
  reg        last;
  reg        start_1t;
  reg [63:0] data_rot_1t;

  /*****************************************************************************
  * 旋转数据为拼接准备
  *****************************************************************************/
  always @(*)
  begin:b_rotation_comb
  
    reg [63:0] v_data;
  
    v_data = datai;
    // edit
     if(align_rot[2]) v_data = {v_data[31:0],v_data[63:32]};              //地址计算结果为4，则高低32位进行交换
     if(align_rot[1]) v_data = {v_data[47:0],v_data[63:48]};              //地址计算结果为2，则高16位和低48位交换
     if(align_rot[0]) v_data = {v_data[55:0],v_data[63:56]};              //地址计算结果为1，则高8位和低56位交换
    data_rot = v_data;
    
  end 
  
  /*****************************************************************************
  * FSM
  *****************************************************************************/
  always @(posedge clk,negedge rst_n)
  begin:b_fsm_seq
  
    reg [ 3:0]  v_align_rot;
    reg [63:0]  v_mask;
  
    if(rst_n==0)
    begin
    
      data_rot_1t     <= 64'b0;
      start_1t        <= 1'b0;
      last            <= 1'b0;
      first_is_merged <= 1'b0;
      
      align_rot       <= 3'b0;
      align_mask      <= 64'b0;
      
      v_align_rot = 0;
      v_mask      = 0;
    
    end
    else
    begin

      /* 根据目的地址和源地址计算偏移和掩码 */
      v_align_rot = {1'b0,dst_addr};//{1'b0,dst_addr} - {1'b0,src_addr};
      v_mask      = {64{1'b1}};  
      if(v_align_rot[2]) v_mask = {v_mask[31:0],32'b0};
      if(v_align_rot[1]) v_mask = {v_mask[47:0],16'b0};
      if(v_align_rot[0]) v_mask = {v_mask[55:0], 8'b0};

      /* buffer */
      if(datai_en & ~last)
      begin
      
        data_rot_1t         <= data_rot;
        first_is_merged     <= 1'b0;
        if(datai_last) last <= 1'b1;
        
      end
      
      /* start detection */
      start_1t <= start;
      
      /* mask initialisation */
      if(start & ~start_1t)
      begin
      
        align_rot  <= v_align_rot[2:0];
        align_mask <= v_mask;
        
        /* The 'last' signal indicates that the very last incoming data has been captured,
         * and then merge buffer shall not be updated any more. 
         * The 'datao_en' signal remains asserted. The module behing the aligner
         * knows exectly how many word to read from the aligner.
         */
        last       <= 1'b0;
        
        /* determine if the very first sample shall be outputed within the cycle of the 
         * very first incoming data (1st incoming data not merge with second incoming data) or 
         * with the second incoming data (1st incoming data is merged with the second incoming data)
         */
         if(v_align_rot[3])
         
           first_is_merged <= 1'b1;
         
         else
         
           first_is_merged <= 1'b0;
         
      end
      else if(~start & start_1t)
      begin
      
        last <= 0;
      
      end
      
    end
    
  end

  /*****************************************************************************
  * merge
  *****************************************************************************/
  assign datao = data_rot_1t & ~align_mask | 
                 data_rot    &  align_mask;
  
  assign datao_en = last |                      // remains for flush purpose
                    datai_en&~first_is_merged;  // mask very first enable if first ougoing data needs merge.
  
endmodule  

module up_aligner
(
  /*****************************************************************************
  * System
  *****************************************************************************/
  input  wire           clk,
  input  wire           rst_n,

  /*****************************************************************************
  * 
  *****************************************************************************/
  input  wire           start,
  input  wire  [2:0]    src_addr,
  input  wire  [2:0]    dst_addr,

  /*****************************************************************************
  * 
  *****************************************************************************/
  input  wire [63:0]    datai,
  input  wire           datai_en,
  input  wire           datai_last,

  /*****************************************************************************
  * 
  *****************************************************************************/
  output wire [63:0]    datao,
  output wire           datao_en
);

  /*****************************************************************************
  * declarations
  *****************************************************************************/
  /* wires */
  reg [63:0] data_rot;
  
  /* flops */
  reg [ 2:0] align_rot;
  reg [63:0] align_mask;
  reg        first_is_merged;
  reg        last;
  reg        start_1t;
  reg [63:0] data_rot_1t;

  /*****************************************************************************
  * rotation
  *****************************************************************************/
  always @(*)
  begin:b_rotation_comb
  
    reg [63:0] v_data;
  
    v_data = datai;
    // edit
     if(align_rot[2]) v_data = {v_data[31:0],v_data[63:32]};
     if(align_rot[1]) v_data = {v_data[47:0],v_data[63:48]};
     if(align_rot[0]) v_data = {v_data[55:0],v_data[63:56]};
    data_rot = v_data;
    
  end 
  
  /*****************************************************************************
  * FSM
  *****************************************************************************/
  always @(posedge clk,negedge rst_n)
  begin:b_fsm_seq
  
    reg [ 3:0]  v_align_rot;
    reg [63:0]  v_mask;
  
    if(rst_n==0)
    begin
    
      data_rot_1t     <= 64'b0;
      start_1t        <= 1'b0;
      last            <= 1'b0;
      first_is_merged <= 1'b0;
      
      align_rot       <= 3'b0;
      align_mask      <= 64'b0;
      
      v_align_rot = 0;
      v_mask      = 0;
    
    end
    else
    begin

      /* 根据目的地址和源地址计算偏移和掩码 */
      v_align_rot = 4'b0 - {1'b0,src_addr};//{1'b0,dst_addr} - {1'b0,src_addr};
      v_mask      = {64{1'b1}};  
      if(v_align_rot[2]) v_mask = {v_mask[31:0],32'b0};     //如果地址偏移为4，则高32位数据有效
      if(v_align_rot[1]) v_mask = {v_mask[47:0],16'b0};     //如果地址偏移为2，则高48位数据有效
      if(v_align_rot[0]) v_mask = {v_mask[55:0], 8'b0};     //如果地址偏移为1，则高56位数据有效

      /* buffer */
      if(datai_en & ~last)
      begin
      
        data_rot_1t         <= data_rot;
        first_is_merged     <= 1'b0;
        if(datai_last) last <= 1'b1;
        
    end
      
      /* start detection */
      start_1t <= start;
      
      /* mask initialisation */
      if(start & ~start_1t)
      begin
      
        align_rot  <= v_align_rot[2:0];
        align_mask <= v_mask;
        
        /* The 'last' signal indicates that the very last incoming data has been captured,
         * and then merge buffer shall not be updated any more. 
         * The 'datao_en' signal remains asserted. The module behing the aligner
         * knows exectly how many word to read from the aligner.
         */
        last       <= 1'b0;
        
        /* determine if the very first sample shall be outputed within the cycle of the 
         * very first incoming data (1st incoming data not merge with second incoming data) or 
         * with the second incoming data (1st incoming data is merged with the second incoming data)
         */
         if(v_align_rot[3])
         
           first_is_merged <= 1'b1;
         
         else
         
           first_is_merged <= 1'b0;
         
      end
      else if(~start & start_1t)
      begin
      
        last <= 0;
      
      end
      
    end
    
  end

  /*****************************************************************************
  * 根据掩码合并数据，即拼数据
  *****************************************************************************/
  assign datao = data_rot_1t & ~align_mask | 
                 data_rot    &  align_mask;
  
  assign datao_en = last |                      // remains for flush purpose
                    datai_en&~first_is_merged;  // mask very first enable if first ougoing data needs merge.
  
endmodule
  
