%----------------------------------------------------------------------------
%--
%-- Module      :  Main
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\documentclass[oldfontcommands,oneside]{memoir}
%include polycode.fmt
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[british]{babel}
\let\fref\undefined
\let\Fref\undefined
\usepackage{fancyref}
\usepackage{hyperref}
\usepackage{url}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{listings}
\renewcommand{\ttdefault}{txtt}
\renewcommand{\rmdefault}{ugm}

\author{Troels Henriksen (athas@@sigkill.dk)}

\title{TwelfPPR: Prettyprinting Twelf signatures}

% The following macro is useful for hiding code blocks from LaTeX (but
% not GHC).
\long\def\ignore#1{}

\begin{document}

\maketitle

\begin{ignore}
\begin{code}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, PackageImports #-}
\end{code}
\end{ignore}

\begin{code}
module Main () where
import Control.Applicative
import Control.Monad.State
import Data.List

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO

import TwelfPPR.Main
\end{code}

The startup function extends the default (static) configuration with
the values specified by the command line options (if any), and passes
the resulting configuration to the logical entry point.

\begin{code}
main :: IO ()
main = do
  opts  <- getOpt RequireOrder options <$> getArgs
  case opts of
    (opts', [cfg], []) -> do
      let conf = defaultConfig { signature_path = cfg }
      twelfppr =<< foldl (>>=) (return conf) opts'
    (_, nonopts, errs) -> do 
      mapM_ (hPutStrLn stderr) $ map ("Junk argument: " ++) nonopts
      usage <- usageStr
      hPutStrLn stderr $ concat errs ++ usage
      exitFailure
\end{code}

Our command-line options are described as mappings from their short
and long names (eg. \verb'-h' and \verb'--help') to a (monadic)
function that extends the TwelfPPR configuration (taking into
account the option argument if there is one).

\begin{code}
options :: [OptDescr (PPRConfig -> IO PPRConfig)]
options = [optHelp, optVersion, optTwelfBin]
\end{code}

The \verb'--help' option follows standard Unix convention by having
the short name \verb'-h' and immediately terminating TwelfPPR after
running.  The code for generating the option list is factored out into
a definition by itself, because we also wish to display it if the user
specifies an invalid option.

\begin{code}
optHelp :: OptDescr (PPRConfig -> IO PPRConfig)
optHelp = Option ['h'] ["help"]
          (NoArg $ \_ -> do
             hPutStrLn stderr =<< usageStr
             exitSuccess)
          "Display this help screen."

usageStr :: IO String
usageStr = do
  prog <- getProgName
  let header = "Help for TwelfPPR " ++ versionString
  let usage  = prog ++ " [options] FILE"
  return $ usageInfo (header ++ "\n" ++ usage) options

versionString :: String
versionString = "0.1"
\end{code}

The \verb'--version' option is very similar, also terminating
the program after printing the version information.

\begin{code}
optVersion :: OptDescr (PPRConfig -> IO PPRConfig)
optVersion = Option ['v'] ["version"]
             (NoArg $ \_ -> do 
                hPutStrLn stderr ("TwelfPPR " ++ versionString ++ ".")
                hPutStrLn stderr "Copyright (C) 2010 Troels Henriksen."
                exitSuccess)
             "Print version number."
\end{code}

\verb'--twelf-bin' modifies the |PPRConfig| value, setting the
|twelf_bin| field to the parameter option provided on the command
line.

\begin{code}
optTwelfBin :: OptDescr (PPRConfig -> IO PPRConfig)
optTwelfBin = Option ['t'] ["twelf-bin"] (ReqArg set "FILE")
              "Path to the twelf-server binary."
    where set p conf = return $ conf { twelf_bin = p }
\end{code}

%include TwelfPPR/LF.lhs
%include TwelfPPR/Pretty.lhs
%include TwelfPPR/GrammarGen.lhs
%include TwelfPPR/InfGen.lhs
%include TwelfPPR/Parser.lhs
%include TwelfPPR/TwelfServer.lhs
%include TwelfPPR/Reconstruct.lhs
%include TwelfPPR/Main.lhs

\appendix

%include TwelfPPR/Util.lhs

\end{document}
