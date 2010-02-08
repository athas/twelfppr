%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Main
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\begin{ignore}
\begin{code}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, PackageImports #-}
\end{code}
\end{ignore}

\chapter{|TwelfPPR.Main|}

Facilities for solving subproblems do not help much if there is
nothing to tie them together.  That is where |TwelfPPR.Main| enters
the picture: as the level just below TwelfPPR's command-line
interface, it accepts a processed representation of command line
arguments and performs the desired actions.  Only those parameters
that completely circumvent the normal functionality of the program,
such as \texttt{ -v}, are handled outside this module.

\begin{code}
module TwelfPPR.Main ( PPRConfig(..)
                     , defaultConfig
                     , twelfppr ) where
\end{code}

\begin{code}
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M

import System.FilePath

import TwelfPPR.InfGen
import TwelfPPR.LF
import TwelfPPR.GrammarGen
import TwelfPPR.Parser
import TwelfPPR.Pretty
import TwelfPPR.Reconstruct
\end{code}

\section{Configuration}

The information passed to TwelfPPR by the user through command-line
parameters is termed the \textit{configuration}, and completely
specifies the path execution will take (assuming a constant outer
environment).

\begin{code}
data PPRConfig = PPRConfig { 
      twelf_bin      :: String
    , signature_path :: String
    }

defaultConfig :: PPRConfig
defaultConfig = PPRConfig { 
                  twelf_bin = "twelf-server"
                , signature_path = undefined 
                }
\end{code}

\section{Wrapping up the monads}

The modules for grammar generation and textual rendering both use
monads that encapsulate a state.  Hence, we have to provide facilities
for accessing and changing said states in whatever monad we want to
use for the rest of our program.

\begin{code}
data PPREnv = PPREnv { g_gen_env   :: GGenEnv
                     , print_env  :: PrintEnv }

emptyPPREnv :: PPREnv
emptyPPREnv = PPREnv { g_gen_env  = emptyGGenEnv
                     , print_env = emptyPrintEnv }
\end{code}

The |PPR| monad itself is just trivial plumbing.

\begin{code}
newtype PPR a = PPR (StateT PPREnv Identity a)
    deriving (Functor, Monad, MonadState PPREnv)

instance MonadGGen PPR where
    getGGenEnv = gets g_gen_env
    putGGenEnv ge = modify $ \e -> e { g_gen_env = ge }

instance MonadPrint PPR where
    getPrintEnv = gets print_env
    putPrintEnv pe = modify $ \e -> e { print_env = pe }

runPPR :: PPR a -> a
runPPR (PPR m) = runIdentity $ evalStateT m emptyPPREnv
\end{code}

\section{Everything else}

Prettyprinting a signature consists of prettyprinting each type family
definition, along with the terms in that family, as a grammar,
separating each type family with a newline.

\begin{code}
ppr :: Signature -> PPR String
ppr sig = newlines <$> liftM2 (++) prods infs
    where defs = M.toList sig
          newlines = intercalate "\n"
          prods = do 
            mapM_ (pprAsProd sig) . filter (prodRulePossible . snd) $ defs
            rules <- M.toList <$> getsGGenEnv prod_rules
            mapM (uncurry $ prettyProd sig) rules
          infs  = mapM judge nonprods
          nonprods = filter (not . prodRulePossible . snd) $ defs
          judge = (return . prettyJudgement . pprAsJudgement)
\end{code}

\begin{code}
twelfppr :: PPRConfig -> IO ()
twelfppr conf = do str <- readFile cfg
                   either print proc $ parseConfig cfg str
    where cfg = signature_path conf
          proc = (=<<) (either print rprint)
                 . procCfg initDeclState
          rprint s = do sig <- toSignature <$> reconstruct' s
                        putStrLn $ runPPR $ ppr sig
          reconstruct' = reconstruct $ twelf_bin conf
          procCfg _ []     = return $ Right []
          procCfg s (f:fs) = do
            str <- readFile $ replaceFileName cfg f
            case parseSig s f str of
              Left e         -> return $ Left e
              Right (ds, s') -> either Left (Right . (ds++)) <$>
                                procCfg s' fs
\end{code}
