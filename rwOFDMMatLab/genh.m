function FadingCoeff = genh(Framelength,Dop,Tsymbol)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by Outwit, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from Outwit.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                        %
%%     Name: genh.m                                                       %
%%                                                                        %
%%     Description: We generate a unique coefficient of fading with "sum  %
%%      of sinusoides" of the Jakes model.                                %
%%                                                                        %
%%     Parameters:                                                        %
%%          Framelength = Length of the plot                              %
%%          Dop = Maximum frequency of the Doppler effect                 %
%%          Tsymbol = Symbol Duration                                     %
%%                                                                        %
%%                                                                        %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Fdmax = Dop;

N = 100;                                         % Number of incident waves
t = Tsymbol:Tsymbol:Tsymbol*Framelength;         % The variable "time"

Len = length(t);
Theta = rand(1,N)*2*pi;               % Generate the uniform phases
fd = cos(2*pi*((1:N)/N))*Fdmax;        % Generate equal-spaced frequencies from "-Fdmax" to "Fdmax"

E = exp(1j.*(2*pi*fd(:)*t(:)'+repmat(Theta(:),1,Len)));
E = E/sqrt(N);
FadingCoeff = sum(E);

end

