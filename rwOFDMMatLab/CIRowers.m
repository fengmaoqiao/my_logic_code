function [Tap_variances, L, Dop] = CIRpowers(N_SUI, Ts)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by Outwit, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from Outwit.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                        %
%%     Name: CIRpowers.m                                                  %
%%                                                                        %
%%     Description: Originally this function gave back the variances of   %
%%      the different paths or "taps" of the channel multipaths; as well  %
%%      as the length of the channel.                                     %
%%     There are additions that give back the frequency of the doppler    %
%%      effect, since in SUI channels it comes defined.
%%                                                                        %
%%     Parameters:                                                        %
%%      N_SUI : Channel to smiulate.    Ts = Duration of sampling (us);      %
%%                                                                        %
%%l                      %
%%                                                                        %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


[Powers, K, Delays, Dop, Ant_corr,Fnorm] = Parameters_SUI(N_SUI);
Dop = max(Dop);

%% The delays are normalized
  sz = size(Delays);
  
  if (and(sz(1) ~= 1,sz(2) == 1)) 
     Delays = Delays.';
  elseif (and(sz(1) ~= 1,sz(2) ~= 1))
      spritf('Error: The delay must be a vector');
  end
  
  %% Now the delays express themselves in number of samples
  Delays = Delays / Ts;
  
  N_taps = length(Powers);
  Len_cir = 1+ round(max(Delays));
  Tap_variances = zeros(1,Len_cir);
  
  %% Calculate the amplitude of each path.
  sz = size(Powers);
  if (and(sz(1) ~= 1,sz(2) == 1)) 
      Powers = Powers.';
  elseif (and(sz(1) ~= 1,sz(2) ~= 1))
      spritf('Error: The powers must be a vector');
  end
     
  
   Variances = 10.^(Powers/10);
   Variances = Variances /sum(Variances); % Normalize the powers
   
   %% Finally, the discreet CIR is calculated bringing every path to the following sample
   
   for i = 1:N_taps
       Tap_variances(1+round(Delays(i))) = Tap_variances(1+round(Delays(i))) + Variances(i);
   end
   
   L = length(Tap_variances)-1;
   
end
   
  
   
   
   
   
   
   
   
   
   
   
  
  

