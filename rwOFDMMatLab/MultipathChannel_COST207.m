%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by Outwit, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from Outwit.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function chan = MultipathChannel_COST207(Sel_TypeOfChan,fs) 

  dopjakes = doppler.jakes;
 
  dopgauss1 = doppler.bigaussian;
  dopgauss1.CenterFreqGaussian1 = -0.8;
  dopgauss1.CenterFreqGaussian2 = 0.4;
  dopgauss1.SigmaGaussian1 = 0.05;
  dopgauss1.SigmaGaussian2 = 0.1;
  dopgauss1.GainGaussian1 = sqrt(2*pi*(dopgauss1.SigmaGaussian1)^2);
  dopgauss1.GainGaussian2 = 1/10 * sqrt(2*pi*(dopgauss1.SigmaGaussian2)^2);

  dopgauss2 = doppler.bigaussian;
  dopgauss2.CenterFreqGaussian1 = 0.7;
  dopgauss2.CenterFreqGaussian2 = -0.4;
  dopgauss2.SigmaGaussian1 = 0.1;
  dopgauss2.SigmaGaussian2 = 0.15;
  dopgauss2.GainGaussian1 = sqrt(2*pi*(dopgauss1.SigmaGaussian1)^2);
  dopgauss2.GainGaussian2 = 1/10^1.5 * sqrt(2*pi*(dopgauss1.SigmaGaussian2)^2);
  
  ts = 1/fs;
%   c = 3e8;
%   fc = 1.4*1e9;
%   v = 60/3.6;
%   fd = v/c*fc;
  fd = 0;
  
                
   switch (Sel_TypeOfChan)
       case 1                      % Rural Area  
           kFactor = 0.87/0.13;    % Note: we use the value from 3GPP TS 45.005 V7.9.0
           fdLOS = 0.7 * fd;
           RAx4PathDelays = [0.0 0.2 0.4 0.6] * 1e-6;
           RAx4AvgPathGaindB = [0 -2 -10 -20];
%            kFactor = 0;
%            RAx4PathDelays = [   0    10    20    30   40   50   60   70   80   90   110   140   170   200   240   290   340   390] * 1e-9;
%            RAx4AvgPathGaindB = [ 0.0  -0.9  -1.7  -2.6 -3.5 -4.3 -5.2 -6.1 -6.9 -7.8  -4.7  -7.3  -9.9 -12.5 -13.7 -18.0 -22.4 -26.7] *1e-9;

           chan = ricianchan(ts, fd, kFactor, RAx4PathDelays, RAx4AvgPathGaindB, fdLOS);
           
%            % This setting is needed to store quantities used by the channel
%            % visualization tool.
% %            chan.StoreHistory = 1;
%            % After each frame is processed, the channel is not reset: this is
%            % necessary to preserve continuity across frames.
%            chan.ResetBeforeFiltering = 0;
%            % This setting makes the total average power of all path gains be
%            % equal to 1.
%            chan.NormalizePathGains = 1;
           
       case 2                          % Typical Urban
           chan = rayleighchan(ts, fd);

           % Assign profile-specific properties to channel object.
           chan.PathDelays =    [  0.0   0.2   0.6   1.6   2.4   5.0  ] * 1e-6;
           chan.AvgPathGaindB = [   -3     0    -2    -6    -8    -10 ];
           chan.DopplerSpectrum = [dopjakes dopjakes dopjakes dopgauss1 dopgauss2 dopgauss2];
                   
                    
       case 3                           % Bad Urban
           chan = rayleighchan(ts,fd);
           
%            chan.PathDelays =    [  0   0.2   0.4   0.8   1.6   2.2   3.2   5.0   6.0   7.2   8.2   10.0  ].*1e-6; 
%            chan.AvgPathGaindB = [  -7   -3    -1     0    -2    -6    -7    -1    -2    -7   -10    -15  ];
%            chan.DopplerSpectrum = [dopjakes dopjakes dopjakes dopgauss1 dopgauss1 dopgauss2 dopgauss2 dopgauss2 dopgauss2 dopgauss2 dopgauss2 dopgauss2];
           
           chan.PathDelays =    [  0   0.4   1.0   1.6   5.0   6.6].*1e-6; % Simplified 6 paths
           chan.AvgPathGaindB = [ -3     0    -3    -5    -2    -4];
           chan.DopplerSpectrum = [dopjakes dopjakes  dopgauss1 dopgauss1 dopgauss2 dopgauss2];
           
                               
       case 4                           % Hilly Terrain     
%             tau = [    0    0.2   0.4   0.8   1.6   2.0   2.4   15.0   15.2   15.8   17.2   20.0 ].*1e-6; 
%             pdb = [  -10     -8    -6    -4     0     0    -4     -8     -9    -10    -12    -14 ]; 

            
            tau = [  0   0.2   0.4   0.6   15.0   17.2 ].*1e-6; % Simplified 6 paths
            pdb = [  0    -2    -4    -7     -6    -12 ];
            chan = rayleighchan(ts,fd,tau,pdb);
            chan.DopplerSpectrum = [dopjakes dopjakes dopjakes dopjakes dopgauss2 dopgauss2];
                      

%             chan.DopplerSpectrum = [dopjakes dopjakes dopjakes dopgauss1 dopgauss1 dopgauss1 dopgauss2 dopgauss2 dopgauss2 dopgauss2 dopgauss2 dopgauss2];
  
            
            
            
                                               
      otherwise
           error('Unkown channel type!');
   end

