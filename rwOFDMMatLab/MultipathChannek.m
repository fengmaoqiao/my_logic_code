function CIR = MultipathChannel(chantype,chanrand,rms,fs)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% channel models for WLAN
% chantype: 0 (nonselective), 1 (ETSI A), 2 (ETSI B), 3 (ETSI C), 4 (ETSI D), 5 (ETSI E)
%           6 (exponential profile, rms delay spread 100 ns (from 802.11 Handbook))
% chanrand: 0 (fixed static,     fixed  gains, fixed energy 1)
%           1 (burstwise static, random gains, fixed energy 1),
%           2 (burstwise static, random gains, varying energy, average energy 1)


%---------------------------------------------------------------------------------------
% channel delay profile: gains (dB) and delays (ns)
switch chantype                         % channel switch
case 0                                  % nonselective channel
  delns = [0];                          % delay (in ns [1 sample 50 or 12.5 ns])
  powdB = [0];                          % single ray with gain 1
case 1                                  % ETSI channel A (typ. office, NLOS, rms d.s. 50ns)
  delns = [   0    10    20    30   40   50   60   70   80   90   110   140   170   200   240   290   340   390];
  powdB = [ 0.0  -0.9  -1.7  -2.6 -3.5 -4.3 -5.2 -6.1 -6.9 -7.8  -4.7  -7.3  -9.9 -12.5 -13.7 -18.0 -22.4 -26.7];
case 2                                  % ETSI channel B (typ. large open/office, NLOS, rms d.s. 100ns)
  delns = [   0    10    20    30   50   80  110  140  180  230   280   330   380   430   490   560   640   730];
  powdB = [-2.6  -3.0  -3.5  -3.9  0.0 -1.3 -2.6 -3.9 -3.4 -5.6  -7.7  -9.9 -12.1 -14.3 -15.4 -18.4 -20.7 -24.6];
case 3                                  % ETSI channel C (typ. large open space, NLOS, rms d.s. 150ns)
  delns = [   0    10    20    30   50   80  110  140  180  230   280   330   400   490   600   730   880  1050];
  powdB = [-3.3  -3.6  -3.9  -4.2  0.0 -0.9 -1.7 -2.6 -1.5 -3.0  -4.4  -5.9  -5.3  -7.9  -9.4 -13.2 -16.3 -21.2];
case 4                                  % ETSI channel D (same as C but LOS spike, rms d.s. about 140ns)
  delns = [   0    10    20    30   50   80  110  140  180  230   280   330   400   490   600   730   880  1050];
  powdB = [ 0.0 -10.0 -10.3 -10.6 -6.4 -7.2 -8.1 -9.0 -7.9 -9.4 -10.8 -12.3 -11.7 -14.3 -15.8 -19.6 -22.7 -27.6];
case 5                                  
  delns = [   0    10    20    40   70  100  140  190  240  320   430   560   710   880  1070  1280  1510  1760];
  powdB = [-4.9  -5.1  -5.2  -0.8 -1.3 -1.9 -0.3 -1.2 -2.1  0.0  -1.9  -2.8  -5.4  -7.3 -10.6 -13.4 -17.4 -20.9]; 
case 6                                  % exponentially decaying profile (from 802)
%   drms  = RMS;                           % rms delay spread (in ns [1 sample 50 or 12.5 ns])
%   delns = [0:(drms/10):(8*drms)];       % resolution 1/10 and span 8* rms delay spread
%   powdB = 10*log10(exp(-delns/drms));
  Ts = 1/fs*1e9;                        % sampling period in ns
  kmax = round(10*rms/Ts);
  delns = (0:kmax)*Ts;
  power0 = 1-exp(-Ts/rms);
  powerProfile = power0*exp(-delns/rms);
  sigma = sqrt(powerProfile/2);
end
%---------------------------------------------------------------------------------------
% construction of CIR vector in I/Q depending on sampling frequency fs
%.......................................................................................
% parameters
if chantype == 6
    L = kmax+1;
    del = delns*1e-9*fs;
    % del = delns*80e-3;
    amp = sigma.*(randn(1,L)+j*randn(1,L));
else
    L   = length(powdB);                    % number of multipath rays
    del = delns*1e-9*fs;                    % delay vector for I/Q (sampling period = 1/fs s)
    for k=1:L pow(k)=10^(powdB(k)/10); end  % average powers of multipath rays
    pow = pow/sum(pow);                     % average multipath energy normalized to 1
    %.......................................................................................
    % realization of fixed or random multipath amplitude with delay profile pow vs. del
    if chanrand==0                          % fixed static, fixed gains
        amp = sqrt(pow);                      % real-valued fixed gains according to profile
    elseif ismember(chanrand,[1,2])         % burstwise static, random gains
        if chantype==4                        % LOS channel
            amp(1)   = sqrt(pow(1));            % first ray: LOS component (real-val. nonrandom)
            amp(2:L) = randn(1,L-1)+j*randn(1,L-1); % other rays: complex-val. random WGN gains
            amp(2:L) = sqrt(0.5*pow(2:L)).*amp(2:L);% (weighted by average amplitude)
        else                                  % NLOS channel
            amp = randn(1,L)+j*randn(1,L);      % all rays: complex-valued random WGN gains
            amp = sqrt(0.5*pow).*amp;           % (weighted by average amplitude)
        end
    end
end

%.......................................................................................
% CIR: superposition of shifted and weighted sampled pulse responses (in-band)
% pulse here can represent the tx filter, or can be an impulse if filter defined separately
del = round(del);                       % have already upsampled - approximate to nearest sample
N = del(L) + 1 ;
CIR = zeros(1,N);                       % CIR prototype
for l=1:L                               % l-th multipath ray with delay del(l)
  g = zeros(1,N);                       % prototype of l-th CIR component
  g(del(l)+1) = 1;
  CIR = CIR + amp(l)*g;                 % weight and accumulate l-th CIR component
end

