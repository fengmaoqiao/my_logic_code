function [RxSignal] = ChannelAndFilters(TxqDAC);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Script to simulate channel and RF effects on WLAN signal
% from transmit digital filter to analog-to-digital converter inclusive
%
% INPUTS: 
%   TxqDAC   : vector containing transmitted signal (complex) at q*60 MHz
%              unsigned, 8 bits
%   ChanType : integer 0 (nonselective), 1 (ETSI A), 2 (ETSI B), 3 (ETSI C), 4 (ETSI D), 5 (ETSI E) 6 (IEEE)
%   ChanRand : 1 or 2.  Use 1.
%   RMS      : rms delay spread of exponential channel in ns (ignored for other channels)
%   SNR      : AWGN added to give this SNR, calculated over the bandwidth of the signal (8.3 MHz)
%   CarrierOffsetPPM  :   Carrier frequency offset to be added, in PPM.  A carrier of 5 GHz is assumed.
%   ClockOffsetPPM    :   Symbol timing clock offset to be added in PPM.
%   DCOffset          :   complex scalar, added to signal to simulate the I and Q DC offsets
%   IQGain            : 
%   PhaseNoiseRMS     :       
%   AGCError       :
%   AGCDelaySamples   :   delay in synch start due to AGC setting
%
% OUTPUTS:
%   Rx60ADC : digital received signal after ADC
%             signed, 8 bits
%   Rx      : digital received signal after digital receive filter
%             signed, 11 bits          
%

%   deltafcTx   : error in the cut-off frequency of the tx analogue filter

global registerRFDigital registerRx registerTransmit registerRF

iiPacket = registerTransmit.currentPacket;

%------------------------------------------------------------------------------------
%         Channel paramters - channel different for each packet
%------------------------------------------------------------------------------------
SNR = registerTransmit.SNR_v(iiPacket);
ChanType = registerTransmit.ChanType_v(iiPacket);  % 0 (nonselective), 1 (ETSI A), 2 (B), 3 (C), 4 (D), 5 (E), 6 (IEEE exponential)
ChanRand = registerTransmit.ChanRand_v(iiPacket);  % 0 (fixed static, energy 1), 
                                                   % 1 (burstwise static, random gains, fixed energy 1),
                                                   % 2 (burstwise static, random gains, varying energy, average energy 1)
RMS      = registerTransmit.RMS_v(iiPacket);       % RMS delay spread in ns. Used only for IEEE channel, i.e. if ChanType = 6

RadioEffectsOn = registerRF.RadioEffectsOn;
ClockOffsetPPM = registerRF.ClockOffsetPPM(iiPacket);
FrequencyOffsetPPM = registerRF.FrequencyOffsetPPM(iiPacket);
DCOffset = registerRF.DCOffset(iiPacket);
IQGainRx = registerRF.IQGainRx(iiPacket);
IQPhaseRx = registerRF.IQPhaseRx(iiPacket);
IQGainTx = registerRF.IQGainTx(iiPacket);
IQPhaseTx = registerRF.IQPhaseTx(iiPacket);
PhaseNoiseRMS = registerRF.PhaseNoiseRMS(iiPacket);
AGCError = registerRF.AGCError(iiPacket);
PARRx = 11+2+3;   % 2 for dc offset, 3 for AGC inaccuracy

switch ChanType,
  case 0
    chanString = 'AWGN';
  case 1
    chanString = 'ETSI A';
  case 2
    chanString = 'ETSI B';
  case 3
    chanString = 'ETSI C';
  case 4
    chanString = 'ETSI D';
  case 5
    chanString = 'ETSI E';
  case 6
    chanString = sprintf('IEEE Exp %dns RMS',RMS);
end;

Disp('VERBOSE_RF','Channel %s (chan rand %d), SNR %2.1fdB',chanString,ChanRand,SNR);
Disp('VERBOSE_RF','Tx: IQ mismatch gain : %+1.2fdB, IQ mismatch phase : %+1.1f degrees',IQGainTx,IQPhaseTx);
Disp('VERBOSE_RF','Rx: IQ mismatch gain : %+1.2fdB, IQ mismatch phase : %+1.1f degrees',IQGainRx,IQPhaseRx);
Disp('VERBOSE_RF','DC Offset: %+0.3f + j x %+0.3f, Phase Noise: %1.2f degree RMS',real(DCOffset),imag(DCOffset),PhaseNoiseRMS);
Disp('VERBOSE_RF','Clock Offset: %+2.2fppm (%+3.2fkHz), Frequency Offset: %+2.2fppm (%+3.2fkHz)',ClockOffsetPPM,5.0e6*ClockOffsetPPM/1e6,FrequencyOffsetPPM,5.0e6*FrequencyOffsetPPM/1e6);

% Read data from signed or unsigned DAC
if registerRFDigital.C2DISBTX == 0,
  TxqDAC = TxqDAC - 128*(1+j);
end;

DeltaFcTx = 0;
Fi = 60;    % DAC/ADC sampling frequency

% oversampling factor to simulate analog transmission (analog filter effect, multipath channel etc.)
q = registerTransmit.q;          

%-----------------------------------------------------------------------------------------
% Tx analog filtering
%-----------------------------------------------------------------------------------------
[B,A]   = butter(4,(12+DeltaFcTx)/(Fi*q/2));
TxAn    = filter(B,A,TxqDAC);

%-----------------------------------------------------------------------------------------
% Tx I/Q Mismatch
%-----------------------------------------------------------------------------------------
I = real(TxAn);
Q = imag(TxAn);   
IQPhaseTx = IQPhaseTx*pi/180;
IQGainTx = 10^(IQGainTx/20);
% apply half (i.e. sqrt) of total gain mismatch to each rail
I = I*sqrt(IQGainTx);
Q = Q/sqrt(IQGainTx);
TxAn = (I*cos(IQPhaseTx/2)-Q*sin(IQPhaseTx/2)) + i*(Q*cos(IQPhaseTx/2)-I*sin(IQPhaseTx/2));   

%-----------------------------------------------------------------------------------------
%Tx power amplifier
%-----------------------------------------------------------------------------------------
%TxAn = TxAmplifier(TxAn);

%-----------------------------------------------------------------------------------------
%       Propagation Channel (Multipath)
%--------------------------------------------------------------------------
% SigNoise: signal + noise after propagation channel
[SigNoise] = Channel(TxAn, ChanType, ChanRand, RMS, SNR, RadioEffectsOn, Fi);

%-----------------------------------------------------------------------------------------
%       Reception
%--------------------------------------------------------------------------
% rx60ADC : digital received signal after ADC
%           signed, 8 bits
% rx20    : digital received signal after digital receive filter
%           signed, 11 bits          
%
% Paramaters reception:
%   PARRx       : peak to average ratio = 16dB
%   NbitADC     : number of bits in DAC = 8
%   CarrierFrequency
%   deltafcRx


PARRx = 11+2+3+2;   % 2 for dc offset, 3 for AGC inaccuracy
NBitADC = 8;
CarrierFrequency = 5.9e9;   % 5.0 GHz. For converting offset in PPm to hertz
DeltaFcRx = 0;

Fi = 60;                    % ADC sampling rate in MHz

%-----------------------------------------------------------------------------------------
%   Rx analog filtering
%-----------------------------------------------------------------------------------------
% SigNoise = [zeros(1,AGCDelaySamples*q*3) SigNoise zeros(1,16*q*3)];
SigNoise = [zeros(1,16*q*3) SigNoise zeros(1,16*q*3)];
[B,A] = cheby1(5,0.1,(12+DeltaFcRx)/(Fi*q/2)); % 12 MHz cut-off frequency
RxSignal = filter(B,A,SigNoise);

%-----------------------------------------------------------------------------------------
%   Clock offset (by linear interpolation at 60*q MHz)
%-----------------------------------------------------------------------------------------
% maximum offset is 2.5 20 MHz samples .
D = 60*q*2.5;               % number of extra samples, for max offset, longest packet, at sampling rate 60*q.
ClockOffset = -ClockOffsetPPM*[1:(length(RxSignal))]/1e6;
Sig2 = [zeros(1,D) RxSignal zeros(1,D)];
% Sig2 = [RxSignal zeros(1,2*D)];

n = floor(ClockOffset);
m = ClockOffset - n;
n = n + D;

idx = [1:length(n)];
a = Sig2(idx + n);
b = Sig2(idx + n+1);
RxSignal = a + (b-a).*m;

%downsampling by q
RxSignal = RxSignal(1:q:length(RxSignal));

%-----------------------------------------------------------------------------------------
%   Frequency offset
%-----------------------------------------------------------------------------------------
CarrierOffset = CarrierFrequency*FrequencyOffsetPPM/1e6;
RxSignal = FrequencyOffset60(RxSignal, CarrierOffset); % direct conversion radio, otherwise add IF here for low IF

% F = psd(RxSignal);
% L= length(F);
% x = -30:60/L:30-1/L;
% 
% figure
% plot(x,10*log10(abs(fftshift(F))))
% grid
% 
% 
% keyboard

%-----------------------------------------------------------------------------------------
%   Phase noise    (add a phase noise of power PhaseNoiseRMS^2 and bandwith +-100kHz)
%-----------------------------------------------------------------------------------------

% generate a Gaussian noise in the bandwidth [-30,30] MHz
PhaseNoise = randn(size(RxSignal));                                    

% butterworth filter used to limit the bandwidth of the phase noise    
Num = 1.0e-009 *[0.01239106386941   0.06195531934705   0.12391063869410   0.12391063869410 0.06195531934705   0.01239106386941];
Den =           [1.00000000000000  -4.95719235378882   9.82968423185450  -9.74588651353102 4.83148984464377  -0.95809520878192];

% filter thise noise in the bandwidth [-100, 100]kHz
PhaseNoise = filter(Num,Den,PhaseNoise);    

% Power of the filtered noise
% PhaseNoisePow = real(PhaseNoise*PhaseNoise')/length(PhaseNoise);
PhaseNoisePow = 4.3e-3;                                         

%scale the noise to obtain a power of PhaseNoiseRMSdeg^2 degree^2
PhaseNoise = PhaseNoise*PhaseNoisePow^(-1/2)*PhaseNoiseRMS;  

RxSignalAbs = abs(RxSignal);
RxSignalAng = angle(RxSignal);

%add the phase noise to the phase of the signal
RxSignalAng = RxSignalAng + PhaseNoise;     

%reconstitute the signal
RxSignal = RxSignalAbs.*exp(i*RxSignalAng);   

%-----------------------------------------------------------------------------------------
%   Rx IQ Mismatch    
%-----------------------------------------------------------------------------------------
I = real(RxSignal);
Q = imag(RxSignal);   
IQPhaseRx = IQPhaseRx*pi/180;
IQGainRx = 10^(IQGainRx/20);
% apply half (i.e. sqrt) of total gain mismatch to each rail
% RxSignal = I/sqrt(IQGainRx) + i*(Q*cos(IQPhaseRx)-I*sin(IQPhaseRx))*sqrt(IQGainRx);   
I = I*sqrt(IQGainRx);
Q = Q/sqrt(IQGainRx);
RxSignal = (I*cos(IQPhaseRx/2)-Q*sin(IQPhaseRx/2)) + i*(Q*cos(IQPhaseRx/2)-I*sin(IQPhaseRx/2));   

%-----------------------------------------------------------------------------------------
%   AGC
%-----------------------------------------------------------------------------------------
% Scale signal level to ADC target level
% rms target value is -16 dB (11 dB for par, 2 dB for dc,3 dB for agc error)
CrestFactor = PARRx + AGCError;
Var = real(RxSignal*RxSignal')/length(RxSignal);
% RxSignal = RxSignal*(Var*10^(CrestFactor/10)/2)^(-1/2)*2^7;
RxSignal = RxSignal*(Var*10^(CrestFactor/10)/2)^(-1/2);


%-----------------------------------------------------------------------------------------
% DC offset, specified as proportion of rms signal level (with perfect AGC)
%-----------------------------------------------------------------------------------------
% rms target value is -16 dB (11 dB for par, 2 dB for dc,3 dB for agc
% error)
RxSignal = RxSignal + DCOffset*10^(-(PARRx)/20); 



