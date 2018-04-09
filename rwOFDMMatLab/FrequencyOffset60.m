function [shifted] = FrequencyOffset60(signal, frequency_offset);
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Apply a frequency offset to the input signal. Assumes 80 MHz sampling frequency
%
% Inputs:   signal:             the signal to be shifted, complex column vector
%           frequency_offset:   scalar, in Hertz
% Output:   shifted:            the signal shifted in frequency by the offset

len = length(signal);
time = 0:len-1;
time = time*1/60e6;
phase = exp(j*(2*pi*time*frequency_offset)); 
shifted = signal.*phase;

