function [SigNoise] = Channel(TxAn, ChanType, ChanRand, RMS, SNR, RadioEffectsOn, Fi)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Signal after propagation channel (multipath)

% INPUTS
%   txAN     : signal after transmission block
%   chantype : integer 0 (nonselective), 1 (ETSI A), 2 (ETSI B), 3 (ETSI C), 4 (ETSI D), 5 (ETSI E) 6 (IEEE)
%   chanrand : 1 or 2.  Use 1.
%   RMS      : rms delay spread of exponential channel in ns (ignored for other channels)
%   SNR      : AWGN added to give this SNR, calculated over the bandwidth of the signal (8.3 MHz)
%   Fi       : DAC/ADC sampling rate in MHz

% OUTPUTS
%   SigNoise : signal + noise after propagation channel
%              signed, 8 bits

% oversampling factor to simulate analog transmission (analog filter effect...)
if RadioEffectsOn
    q = 8;          
else
    q = 1;
end

%-----------------------------------------------------------------------------------------
%   Signal after propagation channel
%-----------------------------------------------------------------------------------------
% CIR : channel impulse response 

%%%%%%%%%%%%%%%%%%%%% Modified by liuyunyun begin %%%%%%%%%%%%%%%%%%%%%%%%%%

% CIR = MultipathChannel_test(ChanType,ChanRand,RMS,q*Fi*1e6);
% CIR = MultipathChannel_SUI(ChanType,q*Fi*1e6);
CIR = MultipathChannel(ChanType,ChanRand,RMS,q*Fi*1e6);
Sig = conv(TxAn,CIR);
% Sig = filter(CIR,1,TxAn);

% chan = MultipathChannel_COST207(ChanType,q*Fi*1e6);
% 
% Sig = filter(chan,TxAn);

%%%%%%%%%%%%%%%%%%%%% Modified by liuyunyun end %%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------------------
%   AWGN
%-----------------------------------------------------------------------------------------
if(ChanRand == 0 || ChanRand == 1)
    Ps = real(Sig*Sig')/length(Sig);
elseif(ChanRand == 2)
    Ps =  real(TxAn*TxAn')/length(TxAn);
end

Noise = randn(size(Sig)) + 1i*randn(size(Sig));

% noise power in signal band
Pbb = Ps*10^(-SNR/10);

% noise power over whole channel bandwidth (Fi*q MHz )
Pbtot = ((Fi*q/20)*64/53)*Pbb;
Noise = sqrt(Pbtot/2)*Noise;


%-----------------------------------------------------------------------------------------
%   Signal + Noise
%-----------------------------------------------------------------------------------------
SigNoise =  Sig + Noise;

