function SimulationSetting(varargin)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   This source code is (C) by RivieraWaves, any copy is strictly forbidden unless 
%     explicitly authorized by a written document originating from RivieraWaves.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

global simulation

global NO_PATTERN
NO_PATTERN = 0;

simulation.writeFile    = 0;
simulation.writeResults = 0;
simulation.useSemaphore = 0;
simulation.readFile     = 0;
simulation.fileName     = 'sprintf(''Files/Rx20_%04d.txt'',iiFile-1)';
simulation.fileNameResults = 'sprintf(''Files/Comp/MatlabResults/File_%04d.txt'',iiFile-1)';

bypass = 0;
for iiArg = 1:nargin,
  if bypass,  % in case of multiple arguments parameters (i.e ...,'FILENAME','directory/file.txt',... )
    bypass = bypass - 1;
  else
    if strcmpi(varargin{iiArg},'NO_PATTERN'),
      NO_PATTERN = 1;
    elseif strcmpi(varargin{iiArg},'WRITEFILE'),
      simulation.writeFile = 1;
    elseif strcmpi(varargin{iiArg},'WRITERESULTS'),
      simulation.writeResults = 1;
    elseif strcmpi(varargin{iiArg},'SEMAPHORE'),
      simulation.useSemaphore = 1;
    elseif strcmpi(varargin{iiArg},'READFILE'),
      simulation.readFile = 1;
    elseif strcmpi(varargin{iiArg},'FILENAME'),
      simulation.fileName = varargin{iiArg+1};
      bypass = 1;
    elseif strcmpi(varargin{iiArg},'FILENAMERESULTS'),
      simulation.fileNameResults = varargin{iiArg+1};
      bypass = 1;
    else
      error(sprintf('Bad parameter : string %s',varargin{iiArg}));
    end
  end
end

