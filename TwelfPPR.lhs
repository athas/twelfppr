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
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S

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
            mapM_ (\x -> pprAsProd sig (S.singleton (fst x)) x) . filter (prodRulePossible . snd) $ defs
            rules <- M.toList <$> getsGGenEnv prod_rules
            return $ map (uncurry pprFam) rules
          infs  = mapM (return . pprAsInf sig) . filter (not . prodRulePossible . snd) $ defs
\end{code}

\begin{code}
pprAsInf :: Signature -> (String, FamilyDef) -> String
pprAsInf sig (name, FamilyDef ms) = 
    "[" ++ name ++ "]\n" ++ intercalate "\n" (map rule $ M.toList ms)
    where rule (name, t) = "  " ++ rule' t ++ "   [" ++ capitalise name ++ "]"
          rule' (TyApp k []) = capitalise k
          rule' (TyApp k os) = capitalise k ++ "(" ++ args ++ ")"
              where args = intercalate "," . map prettyObject $ os
          rule' (TyArrow t1 t2) = rule' t1 ++ " => " ++ rule' t2
          rule' (TyCon _ _ t2) = rule' t2
\end{code}

\section{Examples}

Below are sample |Signature| values.

\begin{code}
sample1 = M.fromList
          [("tm", FamilyDef $ M.fromList 
                    [ ("empty", TyApp "tm" [])
                    , ("app", TyArrow (TyApp "tm" []) 
                                (TyArrow (TyApp "tm" []) (TyApp "tm" [])))
                    , ("lam", TyArrow (TyArrow (TyApp "tm" []) (TyApp "tm" []))
                                (TyArrow (TyApp "tm" []) (TyApp "tm" [])))
                    ])
          ]
\end{code}

Prettyprinted as:

\begin{verbatim}
Tm ::= $Tm | App(Tm,Tm) | Empty | Lam($Tm.Tm,Tm)
\end{verbatim}

\begin{code}
sample2 = M.fromList
          [ ("tp", FamilyDef $ M.fromList
                     [ ("arrow", TyArrow (TyApp "tp" []) 
                                  (TyArrow
                                   (TyApp "tp" []) 
                                   (TyApp "tp" [])))
                     , ("unit", TyApp "tp" [])
                     ])
          , ("tm", FamilyDef $ M.fromList 
                    [ ("empty", TyApp "tm" [])
                    , ("app", TyArrow (TyApp "tm" []) 
                                (TyArrow (TyApp "tm" []) (TyApp "tm" [])))
                    , ("lam", TyArrow (TyArrow (TyApp "tm" []) (TyArrow (TyApp "tp" []) (TyApp "tm" [])))
                                (TyApp "tm" []))
                    ])
          ]
\end{code}

Prettyprinted as:

\begin{verbatim}
Tm ::= $Tm | App(Tm,Tm) | Empty | Lam($Tm.$Tp.Tm)
Tp ::= $Tp | Arrow(Tp,Tp) | Unit
\end{verbatim}

\begin{code}
sample3 = M.fromList
          [ ("foo", FamilyDef $ M.fromList
                      [ ("foo_a", TyApp "foo" [])
                      , ("foo_b", TyArrow (TyApp "foo" []) (TyApp "foo" []))
                      ])
          , ("bar", FamilyDef $ M.fromList
                      [ ("bar_a", TyApp "bar" [])
                      , ("bar_b", TyArrow (TyArrow (TyApp "bar" [])
                                                   (TyApp "foo" []))
                         (TyApp "bar" []))
                      ])
          ]
\end{code}

\begin{code}
sample4 = M.fromList
          [ ("tp", FamilyDef $ M.fromList 
                     [ ("arrow", TyArrow (TyApp "tp" [])
                                   (TyArrow (TyApp "tp" []) (TyApp "tp" [])))
                     , ("unit", (TyApp "tp" []))
                     ])
          , ("tm", FamilyDef $ M.fromList 
                     [ ("empty", TyApp "tm" [])
                     , ("app", TyArrow (TyApp "tm" []) 
                                 (TyArrow (TyApp "tm" []) (TyApp "tm" [])))
                     , ("lam", TyArrow (TyApp "tp" []) 
                                 (TyArrow 
                                  (TyArrow (TyApp "tm" []) (TyApp "tm" []))
                                  (TyArrow (TyApp "tm" []) (TyApp "tm" []))))
                     ])
          , ("value", FamilyDef $ M.fromList
                        [ ("value-empty", TyApp "value" [Type "empty"])
                        , ("value-lam", TyCon "T" (TyApp "tp" [])
                                          (TyCon "E" (TyApp "tm" [])
                                           (TyApp "value"
                                            [(App 
                                              (App (Type "lam") (Type "T"))
                                              (Lambda "x" 
                                               (App (Type "E") (Var "x"))))])))
                         ])
          , ("step", FamilyDef $ M.fromList
                   [ ("step-app-1", 
                      TyCon "E1" (TyApp "tm" [])
                      (TyCon "E1'" (TyApp "tm" [])
                       (TyCon "E2" (TyApp "tm" [])
                        (TyArrow (TyApp "step" 
                                  [Type "E1",
                                   Type "E1'"])
                         (TyApp "step"
                          [ App (App (Type "app") (Type "E1")) 
                            (Type "E2")
                          , App (App (Type "app") (Type "E1'"))
                            (Type "E2")])))))
                   , ("step-app-2",
                      TyCon "E2" (TyApp "tm" [])
                      (TyCon "E2'" (TyApp "tm" [])
                       (TyCon "E1" (TyApp "tm" [])
                        (TyArrow (TyApp "step" 
                                  [Type "E2",
                                   Type "E2'"])
                         (TyArrow (TyApp "value" [Type "E1"])
                          (TyApp "step"
                           [ App (App (Type "app") (Type "E1")) 
                                     (Type "E2")
                           , App (App (Type "app") (Type "E1"))
                             (Type "E2'")]))))))
                   , ("step-app-beta",
                      TyCon "E2" (TyApp "tm" [])
                      (TyCon "T2" (TyApp "tp" [])
                       (TyCon "E" (TyArrow
                                   (TyApp "tm" [])
                                   (TyApp "tm" []))
                        (TyArrow (TyApp "value"
                                  [Type "E2"])
                         (TyApp "step"
                          [ App (App (Type "app")
                                 (App (App (Type "lam") (Type "T2"))
                                  (Lambda "x" (App (Type "E") (Var "x")))))
                            (Type "E2")
                          , App (Type "E") (Type "E2'")])))))
                   ])
          ]
\end{code}

\begin{code}
sample5 = M.fromList
          [ ("foo", FamilyDef $ M.fromList
                      [ ("foo_a", TyApp "foo" [])
                      , ("foo_b", TyArrow (TyApp "bar" []) (TyApp "foo" []))
                      ])
          , ("bar", FamilyDef $ M.fromList
                      [ ("bar_a", TyApp "bar" [])
                      , ("bar_b", TyArrow (TyArrow (TyApp "bar" [])
                                                   (TyApp "foo" []))
                                  (TyApp "bar" []))
                      ])
          , ("baz", FamilyDef $ M.fromList
                      [ ("baz_a", TyArrow (TyApp "bar" []) (TyApp "baz" []))
                      ])
          ]
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
          procCfg s cfg []     = return $ Right []
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

\appendix

%include TwelfPPR/Util.lhs

\end{document}
