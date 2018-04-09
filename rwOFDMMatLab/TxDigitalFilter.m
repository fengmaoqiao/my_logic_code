function Tx60Filt = TxDigitalFilter(Tx)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 
% txDigitalFilter: Transmitter digital filter and upsampling (20 to 60 MHz)
% 
% PURPOSE
%
% Tx60Filt = txDigitalFilter(Tx) performs upsampling from 20 to 60 MHz and 
% the associated interpolation filtering.  Also, the output is scaled to give 
% the correct output level according to the DAC level plan.
%
% INPUTS
%
% Tx  : the input data signal to be filtered.  This should be a complex vector
%       with a sampling rate of 20 MHz, 10 bits signed, with the range -1 to +1.Binary pattern manager.
%
% OUTPUTS
%
% Tx60Filt : the upsampled filtered output, a complex vector, with a sampling
%            rate of 60 MHz, 11 bits signed, range -1 to +1.  This signal 
%            should go to the tx IQ mismatch compensation, or directly to the DAC.
%    
% GLOBAL
%
%   No global or persistent variables are used.
%   
% CONSTANTS
%
%   PARTx : the margin required for the RMS level of the 
%           output signal, compared
%           to full-scale (0 to 1).  Expressed in dB, and should be from the 
%           level plan.  The margin is for the peak-to-average ratio of the 
%           signal, plus any margin for Tx RF effects such as DC offset.
%    
%   RMSTx : The RMS level of the input signal.  This used to scale to the 
%           correct output level.  
%   
% MISCELLANEOUS
%
% In the hardware, this filter uses the same core as the rxDigitalFilter.
% If the output goes directly to the DAC (8 bit) the 3 LSB should be dropped.
%
%     See also RxDigitalFilter.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global registerRFDigital

% 16 bits not necessary for tx(10 OK), but we use same block as rx filter
NBitGT  = 15;

% fixed point FIR filter coefficients (8 bits, signed)
UpFilter = [ 
  -2    -3    -1     2    4     0    -6    -8 ...
  -1     9    12     1  -19   -26    -2    50 ...
 105   127   105    50   -2   -26   -19     1 ...
  12     9    -1    -8   -6     0     4     2 ...
  -1    -3    -2     0  ];

UpFilterHalf = UpFilter(1:18);

L20 = length(Tx);
Tx60 = [reshape(Tx,1,L20);...
        zeros(2,L20)];
Tx60 = reshape(Tx60,1,3*L20);


% fixed point convolution
% length of UpFilter divided by 3
L = 35;
T = toeplitz([Tx60(1:end) zeros(1,L-1)],[Tx60(1),zeros(1,L-1)]);
L60 = size(T,1);

Tadd = T(:,1:18) + [T(:,35:-1:19),zeros(L60,1)];  % 11 bit, no need to saturate or overflow

G   = ones(L60,1) * UpFilterHalf;    % 8 bits 

GT = G .* Tadd;                           % 19 bits

SGT = sum(GT,2);                     % 24 bits

SGTsat = SaturateSgn(floor(SGT * 2^-3), 15);   % 15 bits

% scale signal to DAC target input level, registerTx.TXNORM on 8 bits
Tx60Filt = SGTsat * registerRFDigital.TXNORM;   % sxt to 27 bits

% limit to 8 bits signed, with saturation and rounding
Tx60Filt = (Tx60Filt*2^-13);
Tx60Filt = (Tx60Filt).';


return


