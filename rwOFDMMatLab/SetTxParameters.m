function [PSDUTx] = SetTxParameters(in, dataRateTx)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global parameterTx

if length(in) == 1,
  packetLengthTx = in;
  dataTx = round(rand(1,8*(in-4))); %% 4*8 bits are reserved for CRC check--Lyy
else
  packetLengthTx = floor(length(in) / 2 + 4);
  X = reshape(in,2,length(in)/2)-48;
  A = find((X>=17) & (X<23));
  X(A) = X(A) - 7;
  Y = zeros(8,length(in)/2);
  for ii = 4:-1:1,
    Y(ii,:) = 1 * (X(2,:) >= 2^(ii-1));
    Y(ii+4,:) = 1 * (X(1,:) >= 2^(ii-1));
    X = mod(X,2^(ii-1));
  end;
  dataTx = reshape(Y,1,4*length(in));
end;

FCSTx = FCSGeneration(dataTx); %% this is used for CRC check--Lyy
PSDUTx = [dataTx FCSTx];

% if packetLengthTx < 29,
%   error('Size of PSDU must greater than 28 bytes.');
% elseif packetLengthTx > 2332,
%   error('Size of PSDU must shorter than 2333 bytes.');
% end;

dataRateTxMbpsTable = [ 6  9 12 18 24 36 48 54];
signalRateTxTable   = [ 1 1 0 1; 1 1 1 1; 0 1 0 1; 0 1 1 1;...
                        1 0 0 1; 1 0 1 1; 0 0 0 1; 0 0 1 1];
NBPSCTxTable        = [1 1 2 2 4 4 6 6];
NCBPSTxTable        = [ 48  48  96  96 192 192 288 288];
NDBPSTxTable        = [ 24  36  48  72  96 144 192 216];
codingRateTxTable   = [1 3 1 3 1 3 2 3];  % in function puncturer 1=1/2 2=2/3 3=3/4

dataRateTxMbps = dataRateTxMbpsTable(dataRateTx);
signalRateTx   = signalRateTxTable(dataRateTx,:);
NBPSCTx        = NBPSCTxTable(dataRateTx);
NCBPSTx        = NCBPSTxTable(dataRateTx);
NDBPSTx        = NDBPSTxTable(dataRateTx);
codingRateTx   = codingRateTxTable(dataRateTx);

numSymTx = ceil((16 + 8*packetLengthTx + 6) / NDBPSTx);

parameterTx.packetLengthTx = packetLengthTx;
parameterTx.dataRateTx     = dataRateTx;
parameterTx.dataRateTxMbps = dataRateTxMbps;
parameterTx.signalRateTx   = signalRateTx;
parameterTx.NBPSCTx        = NBPSCTx;
parameterTx.NCBPSTx        = NCBPSTx;
parameterTx.NDBPSTx        = NDBPSTx;
parameterTx.numSymTx       = numSymTx;
parameterTx.codingRateTx   = codingRateTx;


