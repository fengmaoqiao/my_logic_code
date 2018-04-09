function CIR = MultipathChannel_SUI(N_SUI,fs)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by Outwit, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from Outwit.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% channel models for SUI
% N_SUI: 1 (SUI-1), 2 (SUI-2), 3 (SUI-3), 4 (SUI-4), 5 (SUI-5), 6 (SUI-6)
%           
% fs: sample frequency(Hz)

% We are going to consider that we are sending a unique symbol
FrameLength = 1;   
Nfft = 64;

Tsample = 1/(fs*1e-6);       % Duration of sampling (us);
DeltaF = 312.5*1e6;          % Subcarrier spacing 1/3.2(us)
Tb = 1/DeltaF;               % Useful symbol time (data only)
Tsymbol = Tb*(1+1/4);        % OFDM  symbol time (data + cyclic prefix)

[Variances, Lc, Dop] = CIRpowers(N_SUI, Tsample);

hfr = [];
for ih = 1:Lc+1
    hfr = [hfr;genh(FrameLength,Dop,Tsymbol)];
end
hfr = diag(Variances .^ 0.5)*hfr;

 %% hfr has a size of (Lc+1)x(FrameLength)
 %% hfr(:,i) It contains the CIR(Channel Impulse Response) corresponding to the transmission of symbol i

 CIR = hfr./norm(hfr);
end

