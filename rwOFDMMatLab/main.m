%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
%  Main  Computes packet error rate (PER)
% 
% PURPOSE
%
%   Main computes the packet error rate for various SNR and channel type.
%   Generates 1 packet at a time and determines if packet errors occur
%   Averages number of erroneous packets
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear all
SimulationSetting('NO_PATTERN');


%%%%%%%%%%%%%%%%%%%%%%%%%%%%% modified by lyy begin
tic;
disp(sprintf('The game start at: %s',datestr(now)));
warning('off');
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% modified by lyy end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Conditions of simulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% set seeds for all random number generators
rand('state',sum(100*clock));   % sets the seed to a different state each time
randn('state',sum(100*clock));  % sets the seed to a different state each time

% set path
addpath(genpath('channel'));
addpath(genpath('codec'));
addpath(genpath('common'));
addpath(genpath('Rx'));
addpath(genpath('Tx'));

% Backup filename
filename = sprintf('Files/asv_%s_%s.mat',mfilename,strrep(strrep(datestr(now),' ','_'),':','-'));

readFromBackup = false;

if readFromBackup
  load('filename');
else

%% Set Tx parameters
  % Data rate :
  % 1 -  6Mbps, 2 -  9Mbps, 3 - 12Mbps, 4 - 18Mbps, 
  % 5 - 24Mbps, 6 - 36Mbps, 7 - 48Mbps, 8 - 54Mbps
  % DataRate = 8;  % orignal 8 -- liuyunyun
  
  %%%%%%%%%%%%%%%%%%%%%%%% modified by lyy begin
  DataRateV = 1;
  %%%%%%%%%%%%%%%%%%%%%%%% modified by lyy end
  
  % Packet length, in bytes
  % Min: 29, Max: 2332, Special packets: 14
  PacketLength = 1000;  % orignal 29 -- liuyunyu

  
%% set Channel parameters
  % Channel type
  % 0 - AWGN,        1 - ETSI BRAN A, 2 - ETSI BRAN B, 3 - ETSI BRAN C
  % 4 - ETSI BRAN D, 5 - ETSI BRAN E, 6 - IEEE Exponential
  ChanType = 1;  % orignal 0 -- liuyunyun
  dRMS = 50; % RMS Delay spread in ns for IEEE Exponential channel type

  % Noise distribution
  % 0 - fixed static,     fixed xix gains, fixed energy 1
  % 1 - burstwise static, random gains, fixed energy 1
  % 2 - burstwise static, random gains, varying energy, average energy 1
  
  
  ChanRand = 2;  % orignal 2 -- liuyunyu

  % Noise definition
  SNR_v = [32:3:35];  % orignal [22:1:30] -- liuyunyu

%% Set Simulation parameters
  NMinPacket = 20;
  NMaxPacket = 10000; % orignal 200 -- liuyunyu
  NMaxError  = 10000; % orignal 10 -- liuyunyu
  MinPER     = 10^-10; % orignal 10^-2 -- liuyunyu
  DispTime   = 10; % in second

%% Simulation loops
  NPacket = zeros(1,length(SNR_v));
  NError  = zeros(1,length(SNR_v));
  %%%%%%%%%%%%%%%%%%%%%% modified by lyy begin
  NBiterrsum = zeros(1,length(SNR_v));
  %%%%%%%%%%%%%%%%%%%%%% modified by lyy end

 % RegisterPreset(PacketLength, DataRate);
  
  iiSNR = 0;
  nextSNR = true;  

end

%%%%%%%%%%%%%%%%%%%%%%%% modified by lyy begin
for NDataRate = 1:length(DataRateV)
    DataRate = DataRateV(NDataRate);
    nextSNR = true;
    iiSNR = 0;
    NPacket = zeros(1,length(SNR_v));
    NError  = zeros(1,length(SNR_v));
    NBiterrsum = zeros(1,length(SNR_v));
    RegisterPreset(PacketLength, DataRate);
%%%%%%%%%%%%%%%%%%%%%%%% modified by lyy end

while nextSNR
  tic;
  
  iiSNR = iiSNR + 1;
  
  SNR = SNR_v(iiSNR);
  
  nextPacket = true;

  while (nextPacket)
    RadioEffectsOn = RadioSetting('RADIOEFFECTSOFF');

    % Tx
    [Tx,PSDUTx] = TxFixedPt(PacketLength, DataRate);
    [TxqDAC]    = TxFrontEnd(Tx);
    [TxAn]      = TxRF(TxqDAC);
    
    % Channel
    [RxAn] = Channel(TxAn, ChanType, ChanRand, dRMS, SNR, RadioEffectsOn, 60);
    
    % Rx
    [Rx60ADC] = RxRF(RxAn);
    [Rx20HiSS,Rx60ADC,RSSI60] = RxFrontEnd(Rx60ADC);
    [RxData,RxPSDU,RxOK,RxFCS,LQM] = RxModem(Rx20HiSS);
     
    
    % count the number of error bit
    %%%%%%%%%%%%%%%%%% modified by Lyy begin
    if isempty(RxPSDU)
        NBiterr = PacketLength * 8 -32;
    else
        NBiterr = length(find(RxPSDU(1:end-32) ~= PSDUTx(1:end-32)));
    end
    NBiterrsum(iiSNR) = NBiterrsum(iiSNR) + NBiterr;
    %%%%%%%%%%%%%%%%%% modified by Lyy begin
    
    NPacket(iiSNR) = NPacket(iiSNR) + 1;
    if RxOK ~= 1
      NError(iiSNR) = NError(iiSNR) + 1;
    end
    
    
    nextPacket = (NPacket(iiSNR) < NMaxPacket) && ((NError(iiSNR) < NMaxError) || (NPacket(iiSNR) < NMinPacket));
    
%     if toc > DispTime
%       disp('| SNR (dB) | NErr | NPkt | PER (%) |');
%       for ii = 1:iiSNR
%         disp(sprintf('| %8.2f |%5d |%5d | %7.3f |',SNR_v(ii),NError(ii),NPacket(ii),100*NError(ii)/NPacket(ii)));
%       end
%       disp(' ');
%       tic;
%     end
  end
      
filename = ['NumBitErr_DR' num2str(DataRate) 'Ch' num2str(ChanType),'.mat'];
save(filename,'NBiterrsum')
  
%   disp('| SNR (dB) | NErr | NPkt | PER (%) |');
%   for ii = 1:iiSNR
%     disp(sprintf('| %8.2f |%5d |%5d | %7.3f |',SNR_v(ii),NError(ii),NPacket(ii),100*NError(ii)/NPacket(ii)));
%   end
%   disp(' ')

  disp('| SNR (dB) | NBitErr | NBit | PER (%) |');
  for ii = 1:iiSNR
    disp(sprintf('| %8.2f |%5d   |%5d | %7.3f |',SNR_v(ii),NBiterrsum(ii),NPacket(ii)*(PacketLength*8-32),100*NBiterrsum(ii)/ NPacket(ii)*(PacketLength*8-32)));
  end
  disp(' ');
  
  if NError(iiSNR)/NPacket(iiSNR) > MinPER
    nextSNR = iiSNR < length(SNR_v);
  else
    nextSNR = false;
  end
  
%   save(filename);
  
end

%%%%%%%%%%%%%%%%%%%%%% modified by lyy begin
disp('| DataRate | SNR (dB) | NPacErr | NBitErr | NPkt | PER (%) | BER (%) |');
for ii = 1:iiSNR
    disp(sprintf('|   %5d  | %8.2f |  %5d  |  %5d  |%5d | %7.3f | %7.3f |',DataRate, SNR_v(ii),NError(ii),NBiterrsum(ii),NPacket(ii),100*NError(ii)/NPacket(ii),100*NBiterrsum(ii)/(NPacket(ii)*(8*PacketLength-32))));
end
disp(' ');
%%%%%%%%%%%%%%%%%%%%%% modified by lyy end

%%%%%%%%%%%%%%%%%%%%%% modified by lyy begin
%figure
%semilogy(SNR_v(1:iiSNR),NError(1:iiSNR)./NPacket(1:iiSNR));

% figure
% semilogy(SNR_v(1:iiSNR),NError(1:iiSNR)./NPacket(1:iiSNR));
% grid on
% xlabel('SNR (dB)');
% ylabel('PER');
% title(sprintf('PER = f(SNR), DR%d, PL%d, Ch%d.%d',DataRate,PacketLength,ChanType,ChanRand));

figure;
semilogy(SNR_v(1:iiSNR),NBiterrsum(1:iiSNR)./(NPacket(1:iiSNR)*(8*PacketLength-32)));
grid on
xlabel('SNR (dB)');
ylabel('BER');
title(sprintf('BER = f(SNR), DR%d, PL%d, Ch%d.%d',DataRate,PacketLength,ChanType,ChanRand));

end 

disp(sprintf('the game end at: %s', datestr(now)));
toc

% grid on
% xlabel('SNR (dB)');
% ylabel('PER');
% title(sprintf('PER = f(SNR), DR%d, PL%d, Ch%d.%d',DataRate,PacketLength,ChanType,ChanRand));

%%%%%%%%%%%%%%%%%%%%%% modified by lyy end
    


