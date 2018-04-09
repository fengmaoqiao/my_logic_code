function [TxqDAC,Tx60DAC] = TxFrontEnd(Tx)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global registerRFDigital registerTransmit

Tx = [Tx zeros(1,100)];
%-----------------------------------------------------------------------------------------
%       Transmission
%--------------------------------------------------------------------------
% 
% Transmission parameters:
%   NbitDAC     : number of bits in DAC = 8

NBitDAC = 8;

%-----------------------------------------------------------------------------------------
% Tx digital filtering
%-----------------------------------------------------------------------------------------
% input 10 bits signed, output 11 bits signed.
Tx60Filt = TxDigitalFilter(Tx);
PatternBin('Files/Tx','inTxFilter',Tx,10,0,[0 1 2 3]);
PatternBin('Files/Tx','outTxFilter',Tx60Filt,8,0,[0 1 2 3]);

% IQ Mismatch compensation
% Specific I/Q mismatch compensation on 8 bit
Tx60IQ = IQMismatchCompensationTx(Tx60Filt);

% oversampling factor to simulate analog transmission (analog filter effect, multipath channel etc.)
q = registerTransmit.q;          

%-----------------------------------------------------------------------------------------
% DAC
%-----------------------------------------------------------------------------------------
if registerRFDigital.C2DISBTX == 1,
  Tx60DAC = SaturateSgn(Round(Tx60IQ),NBitDAC);
else
  Tx60DAC = SaturateSgn(Round(Tx60IQ),NBitDAC) + 2^(NBitDAC-1)*(1+j);
  
end
Tx60DAC = (Tx60IQ  + 2^(NBitDAC-1)*(1+j));

TxqDAC  = ones(q,1)*Tx60DAC;       %oversampled the transmitted signal with a DAC
TxqDAC  = reshape(TxqDAC,1,q*length(Tx60DAC));
% 8 bits signed, q*60 MHz

