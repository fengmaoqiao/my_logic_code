function GlobalDefinition(varargin)

global VERBOSE_SIMU
VERBOSE_SIMU = 0;

global VERBOSE_TIME
VERBOSE_TIME = 0;

global VERBOSE_PATTERN
VERBOSE_PATTERN = 0;

global VERBOSE_IQ
VERBOSE_IQ = 0;

global VERBOSE_RF
VERBOSE_RF = 0;

global VERBOSE_INITSYNC
VERBOSE_INITSYNC = 0;

global VERBOSE_SIGNAL
VERBOSE_SIGNAL = 0;

global VERBOSE_FCS
VERBOSE_FCS = 0;

global VERBOSE_FILE
VERBOSE_FILE = 0;

global VERBOSE_FILE_NEW
VERBOSE_FILE_NEW = 0;

global RESULTS_FILENAME
RESULTS_FILENAME = 'Files/Results/SimuResults.txt';

N = 0;
for iiArg = 1:nargin,
  if N == 0,
  if strcmpi(varargin{iiArg},'SIMU'),
    VERBOSE_SIMU = 1;
  elseif strcmpi(varargin{iiArg},'TIME'),
    VERBOSE_TIME = 1;
  elseif strcmpi(varargin{iiArg},'IQ'),
    VERBOSE_IQ = 1;
  elseif strcmpi(varargin{iiArg},'RF'),
    VERBOSE_RF = 1;
  elseif strcmpi(varargin{iiArg},'INITSYNC'),
    VERBOSE_INITSYNC = 1;
  elseif strcmpi(varargin{iiArg},'SIGNAL'),
    VERBOSE_SIGNAL = 1;
  elseif strcmpi(varargin{iiArg},'FCS'),
    VERBOSE_FCS = 1;
  elseif strcmpi(varargin{iiArg},'PATTERN'),
    VERBOSE_PATTERN = 1;
  elseif strcmpi(varargin{iiArg},'FILE'),
    VERBOSE_NEW_FILE = 1;
    VERBOSE_FILE = 1;
    elseif strcmpi(varargin{iiArg},'FILENAME'),
      RESULTS_FILENAME = eval(varargin{iiArg+1});
      N = 1;
  else
    error('Bad parameter : string %s',varargin{iiArg});
    end
  else
    N = N - 1;
  end
end

