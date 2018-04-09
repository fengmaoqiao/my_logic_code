function [FDdata] = ModulationMappingFixedPt(Data,CodedBitsPerSym,BitsPerSC)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Outputs:       FDdata       fixed point output (e.g. +- 14 42 70 98 for 64 QAM)
%
% one row per OFDM symbol
% SymShape = reshape(Data,NumSyms,CodedBitsPerSym);
% one row per OFDM symbol
% one column per carrier
% third dimension carries the multiple bits per carrier


NumSyms = prod(size(Data))/CodedBitsPerSym;
SymShape = reshape(Data,BitsPerSC,48,NumSyms);
% 0,1 to -1,+1

switch CodedBitsPerSym,
  case 48,   % BPSK
    SymShape_pm = 2*SymShape-1;
    FDdata = 91 * squeeze(SymShape_pm).'; %BPSK - scaling of 91
  case 96,   % QPSK
    SymShape_pm = 2*SymShape-1;
    FDdata = 64 * squeeze(  (SymShape_pm(1,:,:) + j*SymShape_pm(2,:,:))  ).'; %QPSK - scaling of 64
  case 192,  % 16QAM
    table = [-86 -29 86 29]; % gray encoding
    DataReal = squeeze((SymShape(1,:,:)*2+SymShape(2,:,:)))+1 ;
    DataImag = squeeze((SymShape(3,:,:)*2+SymShape(4,:,:)))+1;
    FDreal = table(DataReal);
    FDimag = table(DataImag);                             
    FDdata = (FDreal + j*FDimag).';
  case 288,  % 64QAM
    table = [-98 -70 -14 -42 98 70 14 42]; % gray encoding
    DataReal = squeeze(SymShape(1,:,:)*4 + SymShape(2,:,:)*2 + SymShape(3,:,:)) + 1;
    DataImag = squeeze(SymShape(4,:,:)*4 + SymShape(5,:,:)*2 + SymShape(6,:,:)) + 1;
    FDreal = table(DataReal);
    FDimag = table(DataImag);  
    FDdata = (FDreal + j*FDimag).';
end
% end of function

