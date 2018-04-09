%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   THIS SOURCE CODE IS (C) BY RIVIERAWAVES, ANY COPY IS STRICTLY FORBIDDEN UNLESS 
%     EXPLICITLY AUTHORIZED BY A WRITTEN DOCUMENT ORIGINATING FROM RIVIERAWAVES.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
FUNCTION TXAN = TXRF(TXQDAC)

GLOBAL REGISTERRF REGISTERTRANSMIT REGISTERRFDIGITAL

IQGAINTX = REGISTERRF.IQGAINTX(1);
IQPHASETX = REGISTERRF.IQPHASETX(1);

DELTAFCTX = 0;
FI = 60;    % DAC/ADC SAMPLING FREQUENCY

% OVERSAMPLING FACTOR TO SIMULATE ANALOG TRANSMISSION (ANALOG FILTER EFFECT, MULTIPATH CHANNEL ETC.)
Q = REGISTERTRANSMIT.Q;          

% READ DATA FROM SIGNED OR UNSIGNED DAC
IF REGISTERRFDIGITAL.C2DISBTX == 0,
  TXQDAC = TXQDAC - 128*(1+J);
END;

%-----------------------------------------------------------------------------------------
% TX ANALOG FILTERING
%-----------------------------------------------------------------------------------------
[B,A]   = BUTTER(4,(12+DELTAFCTX)/(FI*Q/2));
TXAN    = FILTER(B,A,TXQDAC);

%-----------------------------------------------------------------------------------------
% TX I/Q MISMATCH
%-----------------------------------------------------------------------------------------
I = REAL(TXAN);
Q = IMAG(TXAN);   
IQPHASETX = IQPHASETX*PI/180;
IQGAINTX = 10^(IQGAINTX/20);
% APPLY HALF (I.E. SQRT) OF TOTAL GAIN MISMATCH TO EACH RAIL
I = I*SQRT(IQGAINTX);
Q = Q/SQRT(IQGAINTX);
TXAN = (I*COS(IQPHASETX/2)-Q*SIN(IQPHASETX/2)) + I*(Q*COS(IQPHASETX/2)-I*SIN(IQPHASETX/2));   


