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
import Control.Monad.Identity
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M

import System.Environment
import System.FilePath

import TwelfPPR.LF
import TwelfPPR.GrammarGen
import TwelfPPR.Parser
import TwelfPPR.Pretty
import TwelfPPR.Reconstruct
import TwelfPPR.Util
\end{code}

\begin{code}
newtype PPR a = PPR (StateT GGenEnv Identity a)
              deriving (Functor, Monad, MonadState GGenEnv)

runPPR :: PPR a -> a
runPPR (PPR m) = runIdentity $ evalStateT m emptyGGenEnv
\end{code}

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
          infs  = mapM (return . pprAsInf sig) . filter (not . prodRulePossible . snd) $ defs
\end{code}

\begin{code}
pprAsInf :: Signature -> (KindRef, FamilyDef) -> String
pprAsInf _ (KindRef name, FamilyDef ms) = 
    "[" ++ name ++ "]\n" ++ intercalate "\n" (map rule $ M.toList ms)
    where rule (TypeRef rname, t) = "  " ++ rule' t ++ "   [" ++ capitalise rname ++ "]"
          rule' (TyApp (KindRef kn) []) = capitalise kn
          rule' (TyApp (KindRef kn) os) = capitalise kn ++ "(" ++ args ++ ")"
              where args = intercalate "," . map prettyObject $ os
          rule' (TyCon Nothing t1 t2) = rule' t1 ++ " => " ++ rule' t2
          rule' (TyCon _ _ t2) = rule' t2
\end{code}

\begin{ignore}
\begin{code}
test :: Signature -> IO ()
test sig = putStrLn $ runPPR $ ppr sig

main :: IO ()
main = do [cfg] <- getArgs
          str    <- readFile cfg
          either print (proc cfg) $ parseConfig cfg str
    where proc cfg = (=<<) (either print rprint)
                     . procCfg initDeclState cfg
          rprint s = test =<< toSignature <$> reconstruct s
          procCfg _ _   []     = return $ Right []
          procCfg s cfg (f:fs) = do
            str <- readFile $ replaceFileName cfg f
            case parseSig s f str of
              Left e         -> return $ Left e
              Right (ds, s') -> either Left (Right . (ds++)) <$>
                                procCfg s' cfg fs
\end{code}
\end{ignore}

%include TwelfPPR/LF.lhs
%include TwelfPPR/Pretty.lhs
%include TwelfPPR/GrammarGen.lhs
%include TwelfPPR/Parser.lhs
%include TwelfPPR/TwelfServer.lhs
%include TwelfPPR/Reconstruct.lhs

\appendix

%include TwelfPPR/Util.lhs

\end{document}
