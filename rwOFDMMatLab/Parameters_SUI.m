function [P,K,tau,Dop,Ant_corr,Fnorm] = Parameters_SUI(N_SUI)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by Outwit, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from Outwit.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                     % 
%%      Name : Parameters_SUI.m                                        %
%%                                                                     %
%%      Function : Following the value of the channel to simulate,     %
%%       the parameters are given back to be able to obtain the        %
%%       simulation.                                                   %
%%                                                                     %
%%                                                                     %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
      
      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
      %                                                           %
      %  The parameters given back are the following:             %
      %                                                           %
      %    P --> Power of each path (dB)                          %
      %    K --> Factor K of the Ricean distribution (Linear)     %
      %    tau --> Delay of each path (microseconds)              %
      %    Dop --> Maximum Doppler frequency (Hertz)              %
      %    Ant_corr --> Coefficient of antenna correlation        %
      %    Fnorm --> Normalizing factor of gain (dB)              %
      %                                                           %
      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
      
      
 switch N_SUI
    case 1
        P = [ 0 -15 -20 ];
        K = [ 4 0 0 ];
        tau = [ 0.0 0.4 0.9 ];
        Dop = [ 0.4 0.3 0.5 ];
        Ant_corr = 0.7;
        Fnorm = -0.1771;
    case 2
        P = [ 0 -12 -15 ];
        K = [ 2 0 0 ];
        tau = [ 0.0 0.4 1.1 ];
        Dop = [ 0.2 0.15 0.25 ];
        Ant_corr = 0.5;
        Fnorm = -0.3930;
    case 3
        P = [ 0 -5 -10 ];
        K = [ 1 0 0 ];
        tau = [ 0.0 0.4 0.9 ];
        Dop = [ 0.4 0.3 0.5 ];
        Ant_corr = 0.4;
        Fnorm = -1.5113;
    case 4
        P = [ 0 -4 -8 ];
        K = [ 0 0 0 ];
        tau = [ 0.0 1.5 4.0 ];
        Dop = [ 0.2 0.15 0.25 ];
%         Dop = [ 0 0 0];
        
        Ant_corr = 0.3;
        Fnorm = -1.9218;
    case 5
        P = [ 0 -5 -10 ];
        K = [ 0 0 0 ];
        tau = [ 0.0 4.0 10.0 ];
        Dop = [ 2.0 1.5 2.5 ];
        Ant_corr = 0.3;
        Fnorm = -1.5113;
    case 6
        P = [ 0 -10 -14 ];
        K = [ 0 0 0 ];
        tau = [ 0.0 14.0 20.0 ];
        Dop = [ 0.4 0.3 0.5 ];
        Ant_corr = 0.3;
        Fnorm = -0.5683;
 end
 
end

