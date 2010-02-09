%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Pretty
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.Pretty|}

This module defines primitives for printing Twelf terms by themselves.

\begin{code}
module TwelfPPR.Pretty ( PrintEnv(..)
                       , emptyPrintEnv
                       , MonadPrint(..)
                       , prettyObject
                       , prettyKindApp
                       , prettyProd
                       , prettyJudgement ) where

import Control.Monad

import Data.List
import qualified Data.Map as M
import Data.Maybe

import TwelfPPR.InfGen
import TwelfPPR.GrammarGen
import TwelfPPR.LF
import TwelfPPR.Util
\end{code}

\begin{code}
prettyObject :: Object -> String
prettyObject (Const (TypeRef tn)) = tn
prettyObject (Var (TypeRef tn))   = tn
prettyObject (Lambda (TypeRef tn) o) =
  "\\" ++ tn ++ "." ++ prettyObject o
prettyObject (App o1 o2) = descend o1 [o2]
  where descend (Var (TypeRef tn)) args =
          tn ++ "[" ++ intercalate "][" (map prettyObject args) ++ "]"
        descend (Const (TypeRef tn)) args =
          tn ++ " " ++ intercalate " " (map prettyObject args)
        descend (App o1' o2') args = descend o1' $ o2' : args
        descend o args =
          prettyObject o ++ " " ++ intercalate " " (map prettyObject args)
\end{code}

\begin{code}
prettyKindApp :: KindRef -> [Object] -> String
prettyKindApp (KindRef kn) [] = kn
prettyKindApp (KindRef kn) os =
  capitalise kn ++ "(" ++
  intercalate ", " (map prettyObject os) ++ ")"
\end{code}

\section{Rendering production rules}

\begin{code}
type NameContext = M.Map KindRef (M.Map FreeVarContext String)

data PrintEnv = PrintEnv 
    { name_context :: NameContext
    }

emptyPrintEnv :: PrintEnv
emptyPrintEnv = PrintEnv { name_context = M.empty }

class Monad m => MonadPrint m where
    getPrintEnv :: m PrintEnv
    putPrintEnv :: PrintEnv -> m ()

    getsPrintEnv :: (PrintEnv -> a) -> m a
    getsPrintEnv f = getPrintEnv >>= \s -> return (f s)

    modifyPrintEnv :: (PrintEnv -> PrintEnv) -> m ()
    modifyPrintEnv f = getPrintEnv >>= \s ->
                            putPrintEnv (f s)
\end{code}

\begin{code}
prettyProd :: MonadPrint m => Signature
           -> KindUsage
           -> ProdRule
           -> m String
prettyProd sig ku (ts, vars) = do
  name  <- namer sig ku
  terms <- mapM (prettySymbol sig) $ M.toList ts
  let terms' = if vars 
               then ('$':capitalise name) : terms
               else terms
  return $ capitalise name ++ " ::= " ++ intercalate " | " terms'
\end{code}

\begin{code}
prettySymbol :: MonadPrint m => Signature
             -> (TypeRef, RuleSymbol)
             -> m String
prettySymbol _ (TypeRef tn, []) = return $ capitalise tn
prettySymbol sig (TypeRef tn, ts) = do
  args <- liftM (intercalate ", ") $ mapM prettyPremise ts
  return $ capitalise tn ++ "(" ++ args ++ ")"
      where prettyPremise ([], (ku, [])) = do
              name <- namer sig ku
              return $ capitalise name
            prettyPremise ([], (ku, os)) = do
              name <- namer sig ku
              return $ capitalise name ++ "(" ++ args ++ ")"
                  where args = intercalate ", " $ map prettyObject os
            prettyPremise (KindRef kn:tms, ka) = do
              more <- prettyPremise (tms, ka)
              return (("$" ++ capitalise kn ++ ".") ++ more)
\end{code}

\begin{code}
namer :: MonadPrint m => Signature -> KindUsage -> m String
namer sig (kr@(KindRef kn), vs) = do
  context <- getsPrintEnv name_context
  case M.lookup kr context of
    Just m  -> case M.lookup vs m of
                 Just n -> return n
                 Nothing -> do
                   let new = newName m
                   modifyPrintEnv $ \s ->
                     s { name_context =
                         M.insert kr (M.insert vs new m) context }
                   return new
    Nothing -> do
      let new = newName M.empty
      modifyPrintEnv $ \s ->
          s { name_context =
              M.insert kr (M.singleton vs new) context }
      return new
    where newName existing
             | vs == c = capitalise kn
             | otherwise = capitalise kn ++ replicate n '\''
             where n = 1 + M.size (M.filterWithKey (\k _ -> k/=c) existing)
          c  = initContext kr fd
          fd = fromJust $ M.lookup kr sig
\end{code}

\section{Rendering inference rules}

\begin{code}
prettyJudgement :: Judgement -> String
prettyJudgement (Judgement (KindRef name) rules) = 
    "[" ++ name ++ "]\n" ++ intercalate "\n" (map ppr $ M.toList rules)
    where ppr (TypeRef rname, rule) = 
            "  " ++ intercalate " => " (ppr' rule) ++ "   [" ++ capitalise rname ++ "]"
          ppr' (InfRule ps con) = map pprPremise ps ++ [pprCon con]
          pprPremise ((_, []), kr, os) = pprCon (kr, os)
          pprPremise ((_, ps), kr, os) =
            "(" ++ 
            (concatMap ((++" ...=>... ") . pprCon) ps) ++ pprCon (kr, os) ++ 
            ")"
          pprCon  = prettyKindRef
\end{code}
