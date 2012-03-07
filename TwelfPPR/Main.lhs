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
  FlexibleContexts, UndecidableInstances #-}
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
import Control.Arrow
import Control.Monad.CatchIO
import Control.Monad.Reader
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M

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
      twelfBin      :: String
    , signaturePath :: String
    , defaultType   :: Maybe FileType
    , ignoreVars    :: Bool
    , annofilePath  :: Maybe String
    , useContexts   :: Bool
    , texcmdPrefix  :: String
    , debug         :: Bool
    }

defaultConfig :: PPRConfig
defaultConfig = PPRConfig { 
                  twelfBin = "twelf-server"
                , signaturePath = undefined
                , defaultType   = Nothing
                , ignoreVars    = False
                , annofilePath  = Nothing
                , useContexts   = False
                , texcmdPrefix  = "TPPR"
                , debug         = False
                }
\end{code}

\section{Wrapping up the monads}

The modules for grammar generation and textual rendering both use
monads that encapsulate a state.  Hence, we have to provide facilities
for accessing and changing said states in whatever monad we want to
use for the rest of our program.

\begin{code}
data PPREnv = PPREnv { gGenEnv  :: GGenEnv
                     , printEnv  :: PrintEnv
                     , printConf :: PrintConf PPR }

emptyPPREnv :: PPREnv
emptyPPREnv = PPREnv { gGenEnv  = emptyGGenEnv
                     , printEnv  = emptyPrintEnv
                     , printConf = emptyPrintConf }
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
    getGGenEnv = gets gGenEnv
    putGGenEnv ge = modify $ \e -> e { gGenEnv = ge }

instance MonadPrint PPR where
    getPrintEnv = gets printEnv
    putPrintEnv pe = modify $ \e -> e { printEnv = pe }
    askPrintConf = gets printConf
    asksPrintConf f = gets (f . printConf)
    withPrintConf f m = do
      old <- gets printConf
      modify (\s -> s { printConf = f old } )
      v <- m
      modify (\s -> s { printConf = old } )
      return v

runPPR :: PPR a -> PPRConfig -> IO a
runPPR (PPR m) conf = evalStateT (runReaderT m conf) =<< env
    where env = envFromConf conf

envFromConf :: PPRConfig -> IO PPREnv
envFromConf conf = do
  pc <- printConfFromConf conf
  return $ emptyPPREnv {
    printConf = pc
  }

printConfFromConf :: PPRConfig -> IO (PrintConf PPR)
printConfFromConf conf =
  return $ emptyPrintConf {
               prettyJudgement = pj
             , premisePrinter  = pp
             }
      where (pj, pp)
                | useContexts conf =
                    (judgementWithContext,
                     premiseWithContext)
                | otherwise         =
                    (judgementNoContext,
                     premiseWithHypoJudgs)
\end{code}

\section{Everything else}

Prettyprinting a signature consists of prettyprinting each type family
definition, along with the types in that family, as either a grammar
or a judgement, separating each type family with a newline.

\begin{code}
ppr :: Signature -> PPR String
ppr sig = do
  prefix <- asks texcmdPrefix
  con <- asks useContexts
  let kenv kr =
        case M.lookup kr (M.fromList irs) of
          Just (InfRules _ k _) -> kargs k
          Nothing -> error "Unknown kind reference"
  prods <- do
    simple <- asks ignoreVars
    let fprod = (pprAsProd sig $
                 if simple then simpleContexter sig
                 else defaultContexter sig)
    mapM_ fprod . filter (prodRulePossible . snd) $ defs
    rules <- M.toList <$> getsGGenEnv prodRules
    prettyAllGrmRules sig prefix rules
  infs  <- prettyAllRules kenv con prefix (map snd irs)
  abbrs <- prettyAllAbbrs prefix $ map (second defAbbrevs) defs
  return $ intercalate "\n" [infs, prods, abbrs]
    where defs = M.toList sig
          irs = map pprinf defs
          pprinf (kr, kd) = (kr, pprAsInfRules (kr, kd))
          kargs KiType = []
          kargs (KiCon _ ty k) = ty : kargs k
\end{code}

\begin{code}
twelfppr :: PPRConfig -> IO ()
twelfppr conf = runPPR m conf
    where m = do
            t     <- getType path
            decls <- case t of
                       CfgFile -> procCfg path
                       ElfFile -> procElf path
            sig   <- toSignature <$> reconstruct' decls
            maybeReadAnnotations
            pret  <- ppr sig
            liftIO (putStrLn pret)
          path = signaturePath conf
          reconstruct' = reconstruct (twelfBin conf) (debug conf)
\end{code}

\begin{code}
maybeReadAnnotations :: PPR ()
maybeReadAnnotations = do
  maf <- asks annofilePath
  case maf of
    Nothing -> return ()
    Just af -> do 
      c <- liftIO $ readFile af
      let annos = either (error . show) id (parseAnnotations af c)
          (pka, pta, ptv, pmv, prs) = prettifiers annos
      modify $ \s -> s {
        printConf = (printConf s) 
                     { prettyTypeApp  = pka
                     , prettyConstApp = pta
                     , prettyTypeVar  = ptv
                     , prettyBoundVar = pmv
                     , prettyProd     = prs } }
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
  def <- asks defaultType
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
