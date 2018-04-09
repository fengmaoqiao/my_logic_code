function y = TxAmplifier(x)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Description:
%
% Simulates a power amplifier's non-linearity.  Uses the Rapp modem (AM/AM conversion)
% as specified in  "OFDM for Wireless Multimedia Communications", Van Nee and Prasad, page 127.
%
% Input:
% x: input signal
% 
% Output
% y: output signal

% Assume 1dB compression point is set to max range of signal
% backoff is input level relative to 1 dB compression point
% Set parameter p in the model (normally around 1 to 3 depending on PA)
p = 2;
PAbackoff = 8;  % in dB

% Set input backoff
IBO = 10^(-PAbackoff/20);

% Normalise input signal 

knorm = sqrt(mean(x.*conj(x)));
z = IBO*x/knorm; 

% Apply non-linearity to input signal

s = 2*p;
y = z./((1+abs(z).^s).^(1/s));
y = knorm*y/IBO;            %back to input level



