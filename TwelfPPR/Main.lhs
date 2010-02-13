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
such as \verb'-v', are handled outside this module.

\begin{code}
module TwelfPPR.Main ( PPRConfig(..)
                     , FileType(..)
                     , defaultConfig
                     , twelfppr ) where
\end{code}

\begin{code}
import Control.Applicative
import Control.Monad.CatchIO
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe

import System.FilePath
import System.IO

import TwelfPPR.InfGen
import TwelfPPR.LF
import TwelfPPR.GrammarGen
import TwelfPPR.Parser
import TwelfPPR.Pretty
import TwelfPPR.PrettyAnno
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
    , default_type   :: Maybe FileType
    , ignore_vars    :: Bool
    , annofile_path  :: Maybe String
    }

defaultConfig :: PPRConfig
defaultConfig = PPRConfig { 
                  twelf_bin = "twelf-server"
                , signature_path = undefined
                , default_type   = Nothing
                , ignore_vars    = False
                , annofile_path  = Nothing
                }
\end{code}

\section{Wrapping up the monads}

The modules for grammar generation and textual rendering both use
monads that encapsulate a state.  Hence, we have to provide facilities
for accessing and changing said states in whatever monad we want to
use for the rest of our program.

\begin{code}
data PPREnv = PPREnv { g_gen_env  :: GGenEnv
                     , print_env  :: PrintEnv
                     , pretty_env :: PrettyEnv PPR }

emptyPPREnv :: PPREnv
emptyPPREnv = PPREnv { g_gen_env  = emptyGGenEnv
                     , print_env  = emptyPrintEnv
                     , pretty_env = emptyPrettyEnv }
\end{code}

The |PPR| monad itself is just trivial plumbing.  We maintain the
mutable environment defined above, expose the read-only program
configuration, and wrap the IO monad.

\begin{code}
newtype PPR a = PPR (ReaderT PPRConfig (StateT PPREnv IO) a)
    deriving (Functor, Monad, 
              MonadState PPREnv, MonadReader
              PPRConfig,  MonadIO, MonadCatchIO)

instance MonadGGen PPR where
    getGGenEnv = gets g_gen_env
    putGGenEnv ge = modify $ \e -> e { g_gen_env = ge }

instance MonadPrint PPR where
    getPrintEnv = gets print_env
    putPrintEnv pe = modify $ \e -> e { print_env = pe }
    askPrettyEnv = gets pretty_env
    asksPrettyEnv f = gets (f . pretty_env)

runPPR :: PPRConfig -> PPR a -> IO a
runPPR conf (PPR m) = evalStateT (runReaderT m conf) emptyPPREnv
\end{code}

\section{Everything else}

Prettyprinting a signature consists of prettyprinting each type family
definition, along with the types in that family, as either a grammar
or a judgement, separating each type family with a newline.

\begin{code}
ppr :: Signature -> PPR String
ppr sig = newlines <$> liftM2 (++) prods infs
    where defs = M.toList sig
          newlines = intercalate "\n"
          prods = do
            simple <- asks ignore_vars
            let fprod = (pprAsProd sig $
                         if simple then simpleContexter sig
                         else defaultContexter sig)
            mapM_ fprod . filter (prodRulePossible . snd) $ defs
            rules <- M.toList <$> getsGGenEnv prod_rules
            mapM (uncurry $ prettyProd sig) rules
          infs  = mapM judge nonprods
          nonprods = filter (not . prodRulePossible . snd) $ defs
          judge = prettyJudgement . pprAsJudgement
\end{code}

\begin{code}
twelfppr :: PPRConfig -> IO ()
twelfppr conf = runPPR conf m
    where m = do
            t     <- getType path
            decls <- case t of
                       CfgFile -> procCfg path
                       ElfFile -> procElf path
            sig   <- toSignature <$> reconstruct' decls
            maybeReadAnnotations
            pret  <- ppr sig
            liftIO (putStrLn pret)
          path = signature_path conf
          reconstruct' = reconstruct $ twelf_bin conf
\end{code}

\begin{code}
maybeReadAnnotations :: PPR ()
maybeReadAnnotations = do
  maf <- asks annofile_path
  case maf of
    Nothing -> return ()
    Just af -> do 
      c <- liftIO $ readFile af
      let annos = either (error . show) id (parseAnnotations af c)
          (pka, pta) = prettifiers annos
      modify $ \s -> s {
        pretty_env = PrettyEnv { prettyKindApp = pka
                               , prettyTypeApp = pta } }
\end{code}

\section{Reading declarations}

Normally, a Twelf signature is defined by a configuration file of the
extension \verb'cfg', which references files containing actual code
that have the extension \verb'elf'.  For user convenience, we would
also like to be able to process \verb'elf'-files directly, as well as
handling files with arbitrary extensions, treating them as either a
configuration or code file, as specified by the user.  To start with,
let us define the two ways in which a file can be processed.

\begin{code}
data FileType = CfgFile
              | ElfFile
\end{code}

We can guess the type of a file based on its extension (ignoring
case).

\begin{code}
fileType :: FilePath -> Maybe FileType
fileType path = case map toLower (takeExtension path) of
                  ".cfg" -> Just CfgFile
                  ".elf" -> Just ElfFile
                  _     -> Nothing
\end{code}

If the user has explicitly indicated a file type, we will use that,
even if the file path has an extension that we recognise.  If no such
type has been provided, and we cannot recognise the path, we print a
warning and assume \verb'cfg'.

\begin{code}
getType :: FilePath -> PPR FileType
getType path = do
  def <- asks default_type
  maybe (maybe arbitrary return (fileType path)) return def
  where arbitrary = do
          liftIO $ hPutStrLn stderr $ msg (takeExtension path)
          return ElfFile
        msg ext = "Extension '" ++ ext ++ 
                  "' not known, defaulting to " ++
                  ".elf (change with --filetype=cfg)"
\end{code}

Reading a list of declarations from a single \verb'elf'-file, given
its path, is somewhat simple, but I choose implement it in terms of a
more general function that takes a starting state.  This way, it can
be reused for reading entire configurations of associated signatures.

\begin{code}
procElf :: MonadIO m => FilePath -> m [Decl]
procElf = liftM fst . procElfFromState initDeclState

procElfFromState :: MonadIO m => 
                    DeclState 
                 -> FilePath
                 -> m ([Decl], DeclState)
procElfFromState s path = do 
  str <- liftIO $ readFile path
  either (error . show) return $ parseSig s path str
\end{code}

It is now trivial to define a function that returns all the
declarations found by the files referred to by some configuration
file.  Note that we interpret the file paths in the configuration as
being relative to the path of the configuration file itself.

\begin{code}
procCfg :: FilePath -> PPR [Decl]
procCfg path = do
  str  <- liftIO $ readFile path
  let conf = parseConfig path str
  either (error . show) (procCfg' initDeclState) conf
    where procCfg' _ []     = return []
          procCfg' s (f:fs) = do
            (ds, s') <- procElfFromState s $ replaceFileName path f
            liftM (ds++) (procCfg' s' fs)
\end{code}
