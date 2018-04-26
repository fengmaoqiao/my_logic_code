module FIFO(Wr_Clk,//write FIFO clock
   input                    nWr,   //write FIFO signal
   input  [Bsize-1:0]       Din,   //write FIFO data
   input                    Rd_Clk,//read  FIFO clock
   input                    nRd,   //read  FIFO signal
   output [Bsize-1:0]       Dout,  //read  FIFO data

   output                   Full,  // 1 = FIFO full
   output                   Empty
    );// 1 = FIFO empty


 reg Full, Empty;
 reg [Bsize-1:0] Buff [Dsize-1:0];              //FIFO的存储空间，可看做一块数组
 reg [Asize:0] Wr_Addr_Bin, Rd_Addr_Bin;        //写、读地址（二进制）
 //写、读地址（格雷码）；用于判断空、满标志；
 //二进制相邻两位，或许需要同时改变多位，而采用格雷码是因为相邻格雷码的转变只改变一位，避免亚稳态发生；
 //因此需要将二进制地址（方便理解）转化为格雷码地址（确保数据安全）
 reg [Asize:0] Sync_Wr_Addr0_Gray, Sync_Wr_Addr1_Gray, Sync_Wr_Addr2_Gray;
 reg [Asize:0] Sync_Rd_Addr0_Gray, Sync_Rd_Addr1_Gray, Sync_Rd_Addr2_Gray;

 wire [Asize-1:0] FIFO_Entry_Addr, FIFO_Exit_Addr;
 wire [Asize:0] Wr_NextAddr_Bin, Rd_NextAddr_Bin;//ASize+1位的地址，最高位用于标志翻转次数，辅助判断空满标志
 wire [Asize:0] Wr_NextAddr_Gray, Rd_NextAddr_Gray;
 wire Asyn_Full, Asyn_Empty;

 parameter
  Dsize = 256, Asize = 8,
  Bsize = 8;//Dsize 表示FIFO的深度（可以存储的数据数量），Asize表示地址位宽，Bsize表示FIFO的宽度（即，数据是几位的）。

////////////这里是对FIFO进行初始化
 initial
 begin
  Full   = 0;
  Empty  = 1;

  Wr_Addr_Bin = 0;
  Rd_Addr_Bin = 0;

  Sync_Wr_Addr0_Gray = 0;
  Sync_Wr_Addr1_Gray = 0;
  Sync_Wr_Addr2_Gray = 0;
  Sync_Rd_Addr0_Gray = 0;
  Sync_Rd_Addr1_Gray = 0;
  Sync_Rd_Addr2_Gray = 0;
 end
////////////////////FIFO数据的写入与输出//////////////////////////////////////
 assign FIFO_Exit_Addr  = Rd_Addr_Bin[Asize-1:0];
 assign FIFO_Entry_Addr = Wr_Addr_Bin[Asize-1:0];

 assign Dout = Buff[FIFO_Exit_Addr];//读数据
 always @ (posedge Wr_Clk)//写数据
 begin
  if (~nWr & ~Full) Buff[FIFO_Entry_Addr] <= Din;
  else              Buff[FIFO_Entry_Addr] <= Buff[FIFO_Entry_Addr];
 end
///////////////////FIFO读写的地址生成器///////////////////////////////////////
 assign Wr_NextAddr_Bin = (~nWr&~Full) ?Wr_Addr_Bin[Asize:0]+1:Wr_Addr_Bin[Asize:0];
 assign Rd_NextAddr_Bin = (~nRd&~Empty)?Rd_Addr_Bin[Asize:0]+1:Rd_Addr_Bin[Asize:0];

 assign Wr_NextAddr_Gray = (Wr_NextAddr_Bin >> 1) ^ Wr_NextAddr_Bin;//二进制转化为格雷码，右移一位并与自己按位异或。
 assign Rd_NextAddr_Gray = (Rd_NextAddr_Bin >> 1) ^ Rd_NextAddr_Bin;

 always @ (posedge Wr_Clk)
 begin
  Wr_Addr_Bin        <= Wr_NextAddr_Bin;
  Sync_Wr_Addr0_Gray <= Wr_NextAddr_Gray;
 end

 always @ (posedge Rd_Clk)
 begin
  Rd_Addr_Bin        <= Rd_NextAddr_Bin;
  Sync_Rd_Addr0_Gray <= Rd_NextAddr_Gray;
 end
///////////////////采用双锁存器把异步信号同步起来/////////////////////////////
 always @ (posedge Wr_Clk)
 begin
  Sync_Rd_Addr2_Gray <= Sync_Rd_Addr1_Gray;//读信号同步到写时钟
  Sync_Rd_Addr1_Gray <= Sync_Rd_Addr0_Gray;
 end

 always @ (posedge Rd_Clk)
 begin
  Sync_Wr_Addr2_Gray <= Sync_Wr_Addr1_Gray;//写信号同步到读时钟
  Sync_Wr_Addr1_Gray <= Sync_Wr_Addr0_Gray;
 end
/////////////////将产生的Full信号和Empty信号同步的各自的时钟域上//////////////
 assign Asyn_Empty = (Rd_NextAddr_Gray==Sync_Wr_Addr2_Gray);
 assign Asyn_Full  = (Wr_NextAddr_Gray=={~Sync_Rd_Addr2_Gray[Asize:Asize-1],
                                          Sync_Rd_Addr2_Gray[Asize-2:0]});//最高的2位取反；格雷码判空，直接比较二者是否完全相同；格雷码判满，必须满足最高位不同，次高位也不同，其余位相同，才满足满的条件；因此将最高的2位翻转，余下不变；

 always @ (posedge Wr_Clk)
 begin
  Full <= Asyn_Full;
 end

 always @ (posedge Rd_Clk)
 begin
  Empty <= Asyn_Empty;
 end
//////////////////////////////////////////////////////////////////////////////
endmodule
