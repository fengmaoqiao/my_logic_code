function [Tx,PSDUTx] = TxFixedPt(PLorDATA,dataRateTx)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 11a transmitter 
% Rate is the data rate specified according to the following table:
%  1 =  6 Mbps,  24 data bits per symbol,  48 coded bits, 1/2 coding, 1 bit per SC
%  2 =  9 Mbps,  36 data bits per symbol,  48 coded bits, 3/4 coding, 1 bit per SC
%  3 = 12 Mbps,  48 data bits per symbol,  96 coded bits, 1/2 coding, 2 bit per SC
%  4 = 18 Mbps,  72 data bits per symbol,  96 coded bits, 3/4 coding, 2 bit per SC
%  5 = 24 Mbps,  96 data bits per symbol, 192 coded bits, 1/2 coding, 4 bit per SC
%  6 = 36 Mbps, 144 data bits per symbol, 192 coded bits, 3/4 coding, 4 bit per SC
%  7 = 48 Mbps, 192 data bits per symbol, 288 coded bits, 2/3 coding, 6 bit per SC
%  8 = 54 Mbps, 216 data bits per symbol, 288 coded bits, 3/4 coding, 6 bit per SC
% PacketLength is the number of bytes of data to be put in the packet 

global parameterTx registerTransmit
if isempty(registerTransmit)
  registerTransmit.NbBSymbol_v = 10;
  registerTransmit.currentPacket = 1;
end
  
PSDUTx = SetTxParameters(PLorDATA,dataRateTx);

% pilot scrambling sequence - standard section 17.3.5.9
% this sequence is rotated by one symbol compared to that in thestandard, as
% it is used only for the data - the first symbol is applied to the signal field directly
pilot_scrambling_sequence = [...
      1  1  1   -1 -1 -1  1   -1 -1 -1 -1    1  1 -1  1 ...
  -1 -1  1  1   -1  1  1 -1    1  1  1  1    1  1 -1  1 ...
   1  1 -1  1    1 -1 -1  1    1  1 -1  1   -1 -1 -1  1 ...
  -1  1 -1 -1    1 -1 -1  1    1  1  1  1   -1 -1  1  1 ...
  -1 -1  1 -1    1 -1  1  1   -1 -1 -1  1    1 -1 -1 -1 ...
  -1  1 -1 -1    1 -1  1  1    1  1 -1  1   -1  1 -1  1 ...
  -1 -1 -1 -1   -1  1 -1  1    1 -1  1 -1    1  1  1 -1 ...
  -1  1 -1 -1   -1  1  1  1   -1 -1 -1 -1   -1 -1 -1  1];
% each term of the pilot_scrambling sequence multiplies the pilots of one symbol, 
% from and including the first data symbol (not including the symbol field)
% PilotsFD are the pilot values before scrambling, corresponding to carriers -21 7  7 21 respectively
PilotsFD = [1 1 1 -1] * 91;       % 91 is the scaling for BPSK modulation
  
% -----------------------------------------------------------------------------------
% generate short preamble, hard coded
ShortPreSymRe = [67  -193   -20   208   134   208   -20  -193    67     3  -114   -18     0   -18  -114     3];
ShortPreSymIm = [67     3  -114   -18     0   -18  -114     3    67  -193   -20   208   134   208   -20  -193];
ShortPreSym = ShortPreSymRe + j*ShortPreSymIm;      % one complex short preamble symbol
ShortPreTD = kron(ones(1,registerTransmit.NbBSymbol_v(registerTransmit.currentPacket)),ShortPreSym);          % ten consecutive symbols

% -----------------------------------------------------------------------------------
% generate long preamble
LongPreSymRe = [228    -7    58   141    31    87  -168   -56   142    78     1  -199   36    85   -33   174 ...
                 91    54   -83  -191   120   101   -88   -82   -51  -177  -185   109   -4  -134   134    18 ...
               -228    18   134  -134    -4   109  -185  -177   -51   -82   -88   101   120 -191   -83    54 ...
                 91   174   -33    85    36  -199     1    78   142   -56  -168    87    31  141    58    -7];
         
LongPreSymIm = [  0  -175  -162   121    41  -128   -80  -155   -38     6  -167   -69   -85  -22   234    -6 ...
                -91   143    57    95   134    21   118   -32  -220   -24   -30  -108    78  168   154   142 ...
                  0  -142  -154  -168   -78   108    30    24   220    32  -118   -21  -134  -95   -57  -143 ...
                 91     6  -234    22    85    69   167    -6    38   155    80   128   -41 -121   162   175];
LongPreSym = LongPreSymRe + j*LongPreSymIm;     % one complex long preamble symbol
LongPreTDGI = [LongPreSym(33:64) LongPreSym LongPreSym];
% -----------------------------------------------------------------------------------
% signal field
% coded (1/2), interleaved then modulated (not scrambled)
% First 4 bits of signal field indicate the rate. These are stored in SignalRateTable.  
% SignalRateTable contains these bits in order of data rate (6,9,12,18,24,36,48,54)
%
% make up the data sent in this field
PacketLength = parameterTx.packetLengthTx;
PacketLengthBits = [...
    bitand(PacketLength,1)     bitand(PacketLength,2)>1   bitand(PacketLength,2^2)>1  bitand(PacketLength,2^3)>1 ...
    bitand(PacketLength,2^4)>1 bitand(PacketLength,2^5)>1 bitand(PacketLength,2^6)>1  bitand(PacketLength,2^7)>1 ...
    bitand(PacketLength,2^8)>1 bitand(PacketLength,2^9)>1 bitand(PacketLength,2^10)>1 bitand(PacketLength,2^11)>1];
ParityBit = rem((sum(PacketLengthBits))+sum(parameterTx.signalRateTx),2);
Tail = zeros(1,6);
SignalField = [parameterTx.signalRateTx 0 PacketLengthBits ParityBit Tail];
SignalFieldCoded = ConvolutionalCoder(SignalField);

% Signal Field always transmitted 6 Mbps BPSK, 48 coded bits per symbol, 1 bit per subcarrier
% 2nd parameter 1 to initialise interleaver
SignalFieldInterleaved = SignalInterleaver(SignalFieldCoded);

% modulation mapping
SignalFieldFD = ModulationMappingFixedPt(SignalFieldInterleaved.',48,1);
SignalFieldFD = SignalFieldFD.';

% add zeros and pilots
pilots = PilotsFD; % scrambling parameter is 1 for the signal field
SignalFieldPadded = [zeros(1,6) SignalFieldFD(1:5) pilots(1) SignalFieldFD(6:18) pilots(2) SignalFieldFD(19:24) 0 ...
        SignalFieldFD(25:30) pilots(3) SignalFieldFD(31:43) pilots(4) SignalFieldFD(44:48) zeros(1,5)];

% inverse FFT
% 2nd argument: 1=inverse FFT
SignalTD = FFTradix248New_Txfloat(fftshift(4*SignalFieldPadded),1);  
% SignalTD = ifft(fftshift(4*SignalFieldPadded));  

PatternBin('Files/Tx/IFFT','inIFFT',fftshift(4*SignalFieldPadded)+j*0.1,10,0,[0 1]);
PatternBin('Files/Tx/IFFT','outIFFT',SignalTD,11,0,[0 1]);

% add guard interval
SignalTDGI = [SignalTD(49:64) SignalTD];

% -----------------------------------------------------------------------------------
%  generate the service field + data
% will be scrambled, coded, interleaved then modulated
ServiceField = [zeros(1,7) zeros(1,9)]; % first seven zero for descrambler initialisation

% use the same Tail as above (6 zeros) to flush the coder
% calculate the number of pad bits (to fill up the last OFDM symbol)
NumData = parameterTx.numSymTx*parameterTx.NDBPSTx;
NumPadBits = NumData - (16+8*parameterTx.packetLengthTx+6);

% concatenate all the bits of the DataField
DataField = [ServiceField PSDUTx Tail zeros(1,NumPadBits)];

% set data scrambler initial state - should be pseudo-random
% Initialize data scrambler - generate pseudo random initial state
% InitState = [0 1 1 0 1 0 1];
InitState = round(rand(1,7));
% InitState = [0 0 0 1 1 1 1]  % h'78

% if InitState is all zeros, set a random bit to 1, otherwise scrambling doesn't work
if sum(InitState) == 0
    InitState(round((rand*6)+1)) = 1;
end

% Scramble the data
DataFieldScrambled = FastScramble(DataField,InitState);

% set tail bits to zeros again
      

% encode the data
DataFieldCoded = ConvolutionalCoder(DataFieldScrambled);

% change code rate from 1/2 to 2/3 or 3/4 if required
DataFieldPunc = Puncturer(DataFieldCoded);

% interleaver needs one row per symbol
% Numsyms should be the same as before if correct puncturing used
% NumSyms2 = length( DataFieldPunc)/CodedBitsPerSymbol;
if (length(DataFieldPunc) / parameterTx.NCBPSTx ~= parameterTx.numSymTx),
    error('Error in number of symbols')
end
% interleave the data
SymData = reshape(DataFieldPunc, parameterTx.NCBPSTx, parameterTx.numSymTx).';
DataFieldInterleaved = DataInterleaver(SymData, 1); % 2nd parameter 1 to initialise interleaver

% convert the data to QAM symbols (48 per OFDM symbol)
DataFieldFD = ModulationMappingFixedPt(DataFieldInterleaved.', parameterTx.NCBPSTx, parameterTx.NBPSCTx);

% scramble the pilots, make a scrambling sequence of multiples of 127, then truncate to number of symbols
NumScrambReps = ceil(parameterTx.numSymTx/127); % number of times to repeat the scrambling sequence 
reps = ones(NumScrambReps,1);
WholeReps = kron(reps,pilot_scrambling_sequence.');
FullScramblingSequence = WholeReps(1:parameterTx.numSymTx);
pilots_scrambled = FullScramblingSequence*PilotsFD;     

% pad with zeros, set DC to 0 and put the scrambled pilots in the data
if parameterTx.numSymTx == 1
  DataFieldPadded = [zeros(6,1);...
                     DataFieldFD(1:5);  pilots_scrambled(1);...
                     DataFieldFD(6:18); pilots_scrambled(2);...
                     DataFieldFD(19:24);0;...
                     DataFieldFD(25:30);pilots_scrambled(3);...
                     DataFieldFD(31:43);pilots_scrambled(4);...
                     DataFieldFD(44:48);...
                     zeros(5,1)].';
else
DataFieldPadded = [zeros(parameterTx.numSymTx,6) ...
                   DataFieldFD(:,1:5)   pilots_scrambled(:,1) ...
                   DataFieldFD(:,6:18)  pilots_scrambled(:,2) ...
                   DataFieldFD(:,19:24) zeros(parameterTx.numSymTx,1) ...
                   DataFieldFD(:,25:30) pilots_scrambled(:,3) ...
                   DataFieldFD(:,31:43) pilots_scrambled(:,4) ...
                   DataFieldFD(:,44:48) ...
                   zeros(parameterTx.numSymTx,5)];
end

numfft = size(DataFieldPadded,1);

% convert to time domain
% 2nd param: 1 indicates IFFT
% this fft doesn't work on matrices, so need loop
for a = 1:numfft 
%     DataTD(a,:) = FFTradix248(fftshift(4*DataFieldPadded(a,:)),1);  % 2nd argument: 1=inverse FFT
   DataTD(a,:) = FFTradix248New_Txfloat(fftshift(4*DataFieldPadded(a,:)),1);  % 2nd argument: 1=inverse FFT
%    DataTD(a,:) = ifft(fftshift(4*DataFieldPadded(a,:)));  % 2nd argument: 1=inverse FFT
    PatternBin('Files/Tx/IFFT','inIFFT',fftshift(4*DataFieldPadded(a,:)),10,0,[1]);
    PatternBin('Files/Tx/IFFT','outIFFT',DataTD(a,:),11,0,[1]);
end

PatternBin('Files/Tx/IFFT','inIFFT',[],11,0,[2 3]);
PatternBin('Files/Tx/IFFT','outIFFT',[],11,0,[2 3]);

% make sure FFT output is signed 10 bit.
% DataTD = Round(DataTD);
% DataTD = SaturateSgn(DataTD,10);

% add guard interval
DataTDGI = [DataTD(:,49:64) DataTD];

% change from matrix (one line per symbol) to vector
DataTDGIvec = reshape(DataTDGI.',1,80*parameterTx.numSymTx);

% concatenate short and long preambles, signal field and data field
Tx = [ShortPreTD LongPreTDGI SignalTDGI DataTDGIvec];

% end of function

