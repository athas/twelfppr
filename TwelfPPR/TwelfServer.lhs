%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.TwelfServer
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\begin{ignore}
\begin{code}
{-# LANGUAGE PackageImports, GeneralizedNewtypeDeriving #-}
\end{code}
\end{ignore}

\chapter{TwelfPPR.TwelfServer}

We run Twelf itself as a subprocess in order to do term
reconstruction.  This is vastly easier than implementing a term
reconstructor ourselves, though it does of course require that Twelf
is available.  This module abstracts away the details of the
procedure.  We use the portable |System.Process| module to start and
control the subprocess.

\begin{code}
module TwelfPPR.TwelfServer ( TwelfMonadT
                            , withTwelfServer
                            , runTwelfCmd
) where

import Control.Applicative
import Control.Monad.Reader

import Data.List

import System.Exit
import System.IO hiding (stdin, stdout)
import System.Process hiding (proc)
\end{code}

We need only a triplet of handles to communicate with a Twelf
subprocess: the standard input, the standard output, and the process
itself.  Communication will consist solely of writing to its standard
input and reading from its standard output.  Fortunately, the wire
protocol is well-documented, and used to implement Twelf's own Emacs
interface.

\begin{code}
data TwelfProc = TwelfProc { twelfStdin :: Handle
                           , twelfStdout :: Handle
                           , twelfProc :: ProcessHandle }
\end{code}

We do not wish to keep a Twelf subprocess running for the entirety of
our own runtime if we only need its services for a short time, yet we
do also not wish to start a new process every time we wish to invoke a
command (and this would also not work if we wished to execute
sequential commands that modify Twelf's stateful environment).  It
follows that we need a facility for performing an action within the
scope of a single running Twelf instance.  This is aptly modelled as a
monad transformer that wraps a reader monad containing the above
mentioned triplet.  The |TwelfMonadT| thus represents an environment
in which we can interact with a running Twelf subprocess.

\begin{code}
newtype TwelfMonadT m a = TwelfMonadT (ReaderT TwelfProc m a)
    deriving (Functor, Monad, MonadReader TwelfProc, MonadIO, MonadTrans)
\end{code}

The Twelf wire protocol is very simple: a command is followed by a
newline, optionally followed by declarations terminated by
\texttt{``\%.''}.  Twelf responds with zero or more lines of output,
terminated by either \texttt{``\%\% ABORT \%\%''} or \texttt{``\%\% OK
  \%\%''} on a line by itself, depending on whether the command
succeeded.  Note that the following implementation assumes that the
standard input stream is unbuffered; otherwise Twelf might never see
our command and we would block indefinitely trying to read the
response.

\begin{code}
runTwelfCmd :: MonadIO m => String -> TwelfMonadT m String
runTwelfCmd cmd = do
  twelfin  <- asks twelfStdin
  twelfout <- asks twelfStdout
  let getresp = do l <- hGetLine twelfout
                   case l of
                     "%% ABORT %%" -> error "Twelf subprocess error"
                     "%% OK %%"    -> return []
                     _ -> (l:) <$> getresp
  liftIO $ hPutStrLn twelfin $ cmd ++ "\n"
  liftIO $ liftM (intercalate "\n") getresp
\end{code}

The final bit of plumbing needed is the function for actually starting
the Twelf server, running the |TwelfMonadT| action, and shutting down
Twelf again.  The only subtle bit is that we run an \textit{empty}
Twelf command first: this is because the server, upon starting up,
prints a small notice followed by the usual \texttt{``\%\% OK \%\%''}
on standard output; executing an empty command (which is ignored by
Twelf) is a simple way to read past this.

\begin{code}
withTwelfServer :: MonadIO m => String -> TwelfMonadT m a -> m a
withTwelfServer bin m = do
  (Just stdin, Just stdout, _, proc) <- 
      liftIO $ createProcess $ CreateProcess
        { cmdspec   = RawCommand bin []
        , cwd       = Nothing
        , env       = Nothing
        , std_in    = CreatePipe
        , std_out   = CreatePipe
        , std_err   = CreatePipe
        , close_fds = True }
  code <- liftIO $ getProcessExitCode proc
  case code of
    Just (ExitFailure e) ->
      error $ "cannot start " ++ bin ++ ": error " ++ show e
    _ -> return ()
  liftIO $ hSetBuffering stdin NoBuffering
  v <- runReaderT m' $ 
       TwelfProc { twelfStdin  = stdin
                 , twelfStdout = stdout
                 , twelfProc   = proc }
  liftIO $ terminateProcess proc
  return v
      where TwelfMonadT m' = runTwelfCmd "" >> m
\end{code}
