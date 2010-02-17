%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Pretty
%-- Copyright   :  (c) Troels Henriksen 2010
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.Pretty|}
\label{chap:twelfppr.pretty}

This module defines primitives for printing Twelf terms by themselves.

\begin{code}
module TwelfPPR.Pretty ( PrintConf(..)
                       , emptyPrintConf
                       , SymPrettifier
                       , Prettifier
                       , PrintEnv(..)
                       , emptyPrintEnv
                       , MonadPrint(..)
                       , defPrettyKindApp
                       , defPrettyTypeApp
                       , defPrettyRuleSym
                       , prettyObject
                       , prettyVar
                       , prettyConst
                       , namer
                       , prettyName
                       , prettyProd
                       , prettyRules
                       , premiseWithEnv
                       , judgementWithEnv
                       , judgementNoEnv
                       , premiseWithContext ) where

import Control.Monad

import Data.Char
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe

import Text.Regex

import TwelfPPR.InfGen
import TwelfPPR.GrammarGen
import TwelfPPR.LF
import TwelfPPR.Util
\end{code}

\begin{code}
type SymPrettifier m =
    Signature -> (TypeRef, RuleSymbol) -> m String
type Prettifier o m = o -> [Object] -> m String
\end{code}

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
defPrettyKindApp :: MonadPrint m => Prettifier KindRef m
defPrettyKindApp (KindRef kn) [] = return $ prettyConst kn
defPrettyKindApp (KindRef kn) os = do
  args <- mapM prettyObject os
  return $ prettyConst kn ++ "(" ++ intercalate ", " args ++ ")"

defPrettyTypeApp :: MonadPrint m => Prettifier TypeRef m
defPrettyTypeApp (TypeRef tn) [] = return $ prettyConst tn
defPrettyTypeApp (TypeRef tn) os = do
  args <- mapM prettyObject os
  return $ prettyConst tn ++ "(" ++ intercalate ", " args  ++ ")"
\end{code}

\begin{code}
prettyObject :: MonadPrint m => Object -> m String
prettyObject (Const tr) =
  pprTypeApp tr []
prettyObject (Var (TypeRef tn)) =
  return $ prettyVar tn
prettyObject (Lambda (TypeRef tn) o) = do
  body <- prettyObject o
  return $ prettyVar tn ++ "." ++ body
prettyObject (App o1 o2) = descend o1 [o2]
  where descend (Var (TypeRef tn)) os = do
          args <- mapM prettyObject os
          return $ prettyVar tn ++ "[" ++ intercalate "][" args ++ "]"
        descend (Const tr) os = pprTypeApp tr os
        descend (App o1' o2') os = descend o1' $ o2' : os
        descend o os = do
          args <- mapM prettyObject os
          o' <- prettyObject o
          return $ o' ++ "\\ " ++ intercalate "\\ " args
\end{code}

\section{Rendering inference rules}

\begin{code}
type InfRulesPrinter m =
    (KindRef -> S.Set (KindRef, [Object]))
        -> JudgementEnv -> Conclusion -> m String

judgementWithEnv :: MonadPrint m => InfRulesPrinter m
judgementWithEnv kenv (_, vs) (kr, os) = do
  liftM2 (++) env (pprKindApp kr os)
      where env | kenv kr /= S.empty  = do
                    vars' <- liftM (concatMap $ \s -> "\\{" ++ s ++ "\\}")
                             (mapM (uncurry pprKindApp) vs)
                    return ("\\Gamma " ++ vars' ++ "\\vdash")
                | otherwise = return ""

judgementNoEnv :: MonadPrint m => InfRulesPrinter m
judgementNoEnv _ _ = uncurry pprKindApp
\end{code}

\begin{code}
prettyRules :: MonadPrint m => (KindRef -> S.Set (KindRef, [Object])) -> InfRules -> m String
prettyRules kenv (InfRules kr@(KindRef name) rules) = do
  rules'   <- mapM ppr $ M.toList rules
  envrules <- mapM pprvar $ S.toList $ kenv kr
  return $ "[" ++ name ++ "]\n" ++ concatMap (++"\n") (rules' ++ envrules)
    where ppr (TypeRef tn, InfRule ps con) = do
            asRule tn $ do
              pp   <- asksPrintConf premisePrinter
              ps'  <- mapM (pp kenv) $ reverse ps
              con' <- pprJudgement kenv (S.empty, []) con
              return ("\\nfrac{\n" ++ intercalate "\n\\quad\n" ps' ++
                      "}{\n" ++ con' ++ "\n}")
          pprvar x@(KindRef kn, _) =
            asRule rulename $ pprJudgement kenv (S.empty, [x]) x
                where rulename = ("Var-" ++ name ++ kn)

asRule :: Monad m => String -> m String -> m String
asRule label body = do
  body' <- body
  return ("\\begin{displaymath}\n" ++ body' ++
          "\\quad" ++ ruleLabel label ++ 
          "\n\\end{displaymath}\n")

type JudgementPrinter m =
    (KindRef -> S.Set (KindRef, [Object]))
    -> Judgement -> m String

premiseWithEnv :: MonadPrint m => JudgementPrinter m
premiseWithEnv kenv ((vs, ps), kr, os) =
  pprJudgement kenv (vs, ps) (kr, os)

premiseWithContext :: MonadPrint m => JudgementPrinter m
premiseWithContext kenv ((_, []), kr, os) = 
  pprJudgement kenv (S.empty, []) (kr, os)
premiseWithContext kenv ((_, ps), kr, os) = do
  con <- pprJudgement kenv (S.empty, []) (kr, os)
  ps'  <- liftM concat $ mapM proc ps
  return $ "{{" ++ ps' ++ "}\\atop" ++ "{\n" ++ con ++ "\n}}"
      where proc p = do p' <- pprJudgement kenv (S.empty, []) p
                        return ("{\\nfrac{}{" ++ p' ++
                                   "}\\atop{\\vdots}}")
\end{code}

\begin{code}
ruleLabel :: String -> String
ruleLabel tn = "\\textsc{" ++ (texescape . capitalise  . pretty) tn ++ "}"
    where pretty ('_':c:s) = '-' : c : pretty s
          pretty (c:s)     = c : pretty s
          pretty []        = []
\end{code}

\section{Monad}

\begin{code}
data PrintConf m = PrintConf 
  { prettyKindApp   :: Prettifier KindRef m
  , prettyTypeApp   :: Prettifier TypeRef m
  , prettyRuleSym   :: SymPrettifier m
  , prettyJudgement :: InfRulesPrinter m
  , premisePrinter  :: JudgementPrinter m
  }

emptyPrintConf :: MonadPrint m => PrintConf m
emptyPrintConf = PrintConf 
  { prettyKindApp   = defPrettyKindApp
  , prettyTypeApp   = defPrettyTypeApp
  , prettyRuleSym   = defPrettyRuleSym
  , prettyJudgement = judgementWithEnv
  , premisePrinter  = premiseWithEnv 
  }
\end{code}

\begin{code}
pprJudgement :: MonadPrint m => InfRulesPrinter m
pprJudgement kenv x y = do
  pj <- asksPrintConf prettyJudgement
  pj kenv x y

pprKindApp :: MonadPrint m => Prettifier KindRef m
pprKindApp kr os = do
  pka <- asksPrintConf prettyKindApp
  pka kr os

pprTypeApp :: MonadPrint m => Prettifier TypeRef m
pprTypeApp tr os = do
  pta <- asksPrintConf prettyTypeApp
  pta tr os
\end{code}

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

    askPrintConf  :: m (PrintConf m)
    asksPrintConf :: (PrintConf m -> a) -> m a
\end{code}

\section{Rendering production rules}

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
  return ("\\begin{tabular}{rl}\n" ++
          prettyName name ++ " ::=& $" ++ 
          intercalate "$\\\\ \n $\\mid$ & $" terms' ++ "$\n" ++
          "\\end{tabular}\n")
\end{code}

\begin{code}
prettySymbol :: MonadPrint m => Signature 
             -> (TypeRef, RuleSymbol)
             -> m String
prettySymbol sig (tr, ts) = do
  prs <- asksPrintConf prettyRuleSym
  prs sig (tr, ts)

defPrettyRuleSym :: MonadPrint m => SymPrettifier m
defPrettyRuleSym _ (TypeRef tn, []) =
  return $ prettyName tn
defPrettyRuleSym sig (TypeRef tn, ts) = do
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
