%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Pretty
%-- Copyright   :  (c) Troels Henriksen 2010
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.Pretty|}

This module defines primitives for printing Twelf terms by themselves.

\begin{code}
module TwelfPPR.Pretty ( PrettyEnv(..)
                       , emptyPrettyEnv
                       , Prettifier
                       , PrintEnv(..)
                       , emptyPrintEnv
                       , MonadPrint(..)
                       , defPrettyKindApp
                       , defPrettyTypeApp
                       , prettyObject
                       , prettyVar
                       , prettyConst
                       , prettyProd
                       , prettyJudgement ) where

import Control.Monad

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe

import Text.Regex

import TwelfPPR.InfGen
import TwelfPPR.GrammarGen
import TwelfPPR.LF
import TwelfPPR.Util
\end{code}

\begin{code}
data PrettyEnv m = PrettyEnv { prettyKindApp :: Prettifier KindRef m
                             , prettyTypeApp :: Prettifier TypeRef m
                             }

type Prettifier o m = o -> [Object] -> m String

emptyPrettyEnv :: MonadPrint m => PrettyEnv m
emptyPrettyEnv = PrettyEnv { prettyKindApp = defPrettyKindApp
                           , prettyTypeApp = defPrettyTypeApp }
\end{code}

\begin{code}
defPrettyKindApp :: MonadPrint m => KindRef -> [Object] -> m String
defPrettyKindApp (KindRef kn) [] = return kn
defPrettyKindApp (KindRef kn) os = do
  args <- mapM prettyObject os
  return $ kindname ++ "(" ++ intercalate ", " args ++ ")"
      where kindname = "\\textrm{" ++ texescape kn ++ "}"

defPrettyTypeApp :: MonadPrint m => TypeRef -> [Object] -> m String
defPrettyTypeApp (TypeRef tn) [] = return tn
defPrettyTypeApp (TypeRef tn) os = do
  args <- mapM prettyObject os
  return $ prettyConst tn ++ "(" ++ intercalate ", " args  ++ ")"

prettyObject :: MonadPrint m => Object -> m String
prettyObject (Const (TypeRef tn)) = 
  return $ prettyConst tn
prettyObject (Var (TypeRef tn))   =
  return $ prettyVar tn
prettyObject (Lambda (TypeRef tn) o) = do
  body <- prettyObject o
  return $ prettyVar tn ++ "." ++ body
prettyObject (App o1 o2) = descend o1 [o2]
  where descend (Var (TypeRef tn)) os = do
          args <- mapM prettyObject os
          return $ prettyVar tn ++ "[" ++ intercalate "][" args ++ "]"
        descend (Const tr) os = do
          pta <- asksPrettyEnv prettyTypeApp
          pta tr os
        descend (App o1' o2') os = descend o1' $ o2' : os
        descend o os = do
          args <- mapM prettyObject os
          o' <- prettyObject o
          return $ o' ++ "\\ " ++ intercalate "\\ " args
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

    askPrettyEnv  :: m (PrettyEnv m)
    asksPrettyEnv :: (PrettyEnv m -> a) -> m a
\end{code}

\begin{code}
prettyName :: String -> String
prettyName s = "\\textrm{" ++ s' ++ "}"
    where s' = texescape $ capitalise s
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
               then ("\\$"++prettyName name) : terms
               else terms
  return $ prettyName name ++ " ::= " ++ intercalate " $\\mid$ " terms' ++ "\n"
\end{code}

\begin{code}
prettySymbol :: MonadPrint m => Signature 
             -> (TypeRef, RuleSymbol)
             -> m String
prettySymbol _ (TypeRef tn, []) = return $ prettyName tn
prettySymbol sig (TypeRef tn, ts) = do
  args <- liftM (intercalate ", ") $ mapM prettyPremise ts
  return $ prettyName tn ++ "(" ++ args ++ ")"
      where prettyPremise ([], (ku, [])) = do
              name <- namer sig ku
              return $ prettyName name
            prettyPremise ([], (ku, os)) = do
              name <- namer sig ku
              args <- liftM (intercalate ", ") $ mapM prettyObject os
              return $ prettyName name ++ "(" ++ args ++ ")"
            prettyPremise (KindRef kn:tms, ka) = do
              more <- prettyPremise (tms, ka)
              return (("\\$" ++ prettyName kn ++ ".") ++ more)
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
             | vs == c = prettyName kn
             | otherwise = prettyName kn ++ replicate n '\''
             where n = 1 + M.size (M.filterWithKey (\k _ -> k/=c) existing)
          c  = initContext kr fd
          fd = fromJust $ M.lookup kr sig
\end{code}

\section{Rendering inference rules}

\begin{code}
prettyConst :: String -> String
prettyConst s = "\\textrm{" ++ texescape s ++ "}"

prettyVar :: String -> String
prettyVar s = case matchRegex r s of
                Just [name, i] -> texescape name ++ "_{" ++ i ++ "}"
                _ -> texescape s
    where r = mkRegex "([^0-9]+)([0-9]+)"
\end{code}

\begin{code}
prettyJudgement :: MonadPrint m => Judgement -> m String
prettyJudgement (Judgement (KindRef name) rules) = do
  rules' <- mapM ppr $ M.toList rules
  return $ "[" ++ name ++ "]\n" ++ concatMap (++"\n") rules'
    where ppr (tr, rule) = do
            rule' <- ppr' rule
            return ("\\begin{displaymath}\n" ++ rule' ++
                    "\\quad" ++ ruleLabel tr ++ "\n\\end{displaymath}\n")
          ppr' (InfRule ps con) = do
            ps'   <- mapM pprPremise $ reverse ps
            con' <- pprCon con
            return ("\\nfrac{\n" ++ intercalate "\n\\quad\n" ps' ++
                    "}{\n" ++ con' ++ "\n}")
          pprPremise ((_, []), kr, os) = pprCon (kr, os)
          pprPremise ((_, ps), kr, os) = do
            con' <- pprCon (kr, os)
            ps'  <- liftM concat $ mapM proc ps
            return $ "{{" ++ ps' ++ "}\\atop" ++ "{\n" ++ con' ++ "\n}}"
                where proc p = do p' <- pprCon p
                                  return ("{\\nfrac{}{" ++ p' ++
                                          "}\\atop{\\vdots}}")
          pprCon (kr, os)  = do pka <- asksPrettyEnv prettyKindApp
                                pka kr os
\end{code}

\begin{code}
ruleLabel :: TypeRef -> String
ruleLabel (TypeRef tn) = "\\textsc{" ++ (texescape . capitalise  . pretty) tn ++ "}"
    where pretty ('_':c:s) = '-' : c : pretty s
          pretty (c:s)     = c : pretty s
          pretty []        = []
\end{code}
