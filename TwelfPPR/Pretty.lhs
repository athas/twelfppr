%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Pretty
%-- Copyright   :  (c) Troels Henriksen 2010
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\begin{ignore}
\begin{code}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
\end{code}
\end{ignore}

\chapter{|TwelfPPR.Pretty|}
\label{chap:twelfppr.pretty}

This module defines primitives for printing Twelf terms by themselves.

\begin{code}
module TwelfPPR.Pretty ( prettyAllRules
                       , prettyAllProds
                       , PrintConf(..)
                       , emptyPrintConf
                       , SymPrettifier
                       , Prettifier
                       , TypeVarPrinter
                       , PrintEnv(..)
                       , emptyPrintEnv
                       , MonadPrint(..)
                       , bindingVar
                       , defPrettyTypeApp
                       , defPrettyBoundVar
                       , defPrettyConstApp
                       , defPrettyTypeVar
                       , defPrettyRuleSym
                       , pprTypeVar
                       , pprObject
                       , prettyVar
                       , prettyConst
                       , prettyName
                       , prettyProd
                       , prettyRules
                       , premiseWithContext
                       , judgementWithContext
                       , judgementNoContext
                       , premiseWithHypoJudgs
                       , splitVar )
    where

import Control.Monad.Reader

import Data.Char
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Data.Monoid

import Text.Regex

import TwelfPPR.InfGen
import TwelfPPR.GrammarGen
import TwelfPPR.LaTeX
import TwelfPPR.LF
\end{code}

\section{Type variables}

\begin{code}
varMap :: MonadPrint m => 
          m (TypeVarPrinter m)
       -> S.Set (TypeRef, Type) 
       -> m (M.Map Type (M.Map TypeRef String))
varMap p s = do
  procVars p $ S.toList s

splitVar :: TypeRef -> (String, Maybe Integer, Int)
splitVar (TypeRef tn) =
  case matchRegex r tn of
    Just [name, "", ps] -> (name, Nothing, length ps)
    Just [name, i, ps]  -> (name, Just $ read i, length ps)
    _                   -> (tn, Nothing, 0)
    where r = mkRegex "([^0-9']+)([0-9]*)('*)"

procVars :: MonadPrint m =>
            m (TypeVarPrinter m)
         -> [(TypeRef, Type)]
         -> m (M.Map Type (M.Map TypeRef String))
procVars p l = do
  vs <- uniqify proc l S.empty
  return $ table vs
    where proc tr ty = do
            pt <- p
            s  <- pt tr ty
            return s
          table = foldl f M.empty
          f m (ty, (tr, s)) =
            M.insertWith (M.union) ty (M.singleton tr s) m

uniqify :: MonadPrint m =>
           TypeVarPrinter m
        -> [(TypeRef, Type)]
        -> S.Set String
        -> m [(Type, (TypeRef, String))]
uniqify _ [] _ = return []
uniqify p ((tr, ty):ts) seen = do
  s <- realUniq p (tr, ty) seen
  more <- uniqify p ts $ s `S.insert` seen
  return $ (ty, (tr, s)):more

realUniq :: MonadPrint m =>
            TypeVarPrinter m
         -> (TypeRef, Type)
         -> S.Set String
         -> m String
realUniq p (tr, ty) seen = do
  s <- p tr ty
  case (s `S.member` seen) of
    True  -> realUniq p (tr', ty) seen
    False -> return s
    where (name, idx, ps) = splitVar tr
          tr' = TypeRef (name ++
                         show idx' ++
                         replicate ps '\'')
          idx' = maybe 1 (1+) idx

cfgVarMaps :: MonadPrint m => 
             S.Set (TypeRef, Type)
          -> S.Set (TypeRef, Type) -> m ()
cfgVarMaps ts ms = do
  vm <- varMap (asksPrintConf prettyTypeVar) ts
  mm <- varMap (asksPrintConf prettyBoundVar) ms
  modifyPrintEnv $ \e -> e { type_vars = vm
                           , bound_vars = mm }
\end{code}

\section{Generalities}

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
defPrettyTypeApp :: MonadPrint m => Prettifier TyFamRef m
defPrettyTypeApp (TyFamRef kn) [] = return $ prettyConst kn
defPrettyTypeApp (TyFamRef kn) os = do
  args <- mapM pprObject os
  return $ prettyConst kn ++ "(" ++ intercalate ", " args ++ ")"

defPrettyConstApp :: MonadPrint m => Prettifier TypeRef m
defPrettyConstApp (TypeRef tn) [] = return $ prettyConst tn
defPrettyConstApp (TypeRef tn) os = do
  args <- mapM pprObject os
  return $ prettyConst tn ++ "(" ++ intercalate ", " args  ++ ")"

type TypeVarPrinter m = TypeRef -> Type -> m String

defPrettyTypeVar :: MonadPrint m => TypeVarPrinter m
defPrettyTypeVar (TypeRef tn) _ = return $ prettyVar tn

defPrettyBoundVar :: MonadPrint m => TypeVarPrinter m
defPrettyBoundVar (TypeRef tn) _ = return $ prettyVar tn
\end{code}

\begin{code}
prettyName :: String -> String
prettyName s = "\\textrm{" ++ s' ++ "}"
    where s' = texescape s
\end{code}

\begin{code}
pprObject :: MonadPrint m => Object -> m String
pprObject (Const tr) =
  pprConstApp tr []
pprObject (Var tr ty) = do
  pprTypeVar tr ty
pprObject (Lambda tr ty o) = bindingVar tr $ do
  body <- pprObject o
  vs <- pprTypeVar tr ty
  return $ vs ++ "." ++ body
pprObject (App o1 o2) = descend o1 [o2]
  where descend (Var tr ty) os = do
          args <- mapM pprObject os
          s    <- pprTypeVar tr ty
          return $ s ++ "[" ++ intercalate "][" args ++ "]"
        descend (Const tr) os = pprConstApp tr os
        descend (App o1' o2') os = descend o1' $ o2' : os
        descend o os = do
          args <- mapM pprObject os
          o' <- pprObject o
          return $ o' ++ "\\ " ++ intercalate "\\ " args
\end{code}

\section{Rendering inference rules}

\begin{code}
type JudgementPrinter m =
    (TyFamRef -> [Type]) -> JudgementEnv -> Conclusion -> m String

judgementWithContext :: MonadPrint m => JudgementPrinter m
judgementWithContext kenv (_, vs) (kr, os) = do
  liftM2 (++) env (pprTypeApp kr os)
      where env | kenv kr /= []  = do
                    vars' <- liftM (concatMap (","++))
                             (mapM (uncurry pprTypeApp) vs)
                    return ("\\Gamma " ++ vars' ++ "\\vdash")
                | otherwise = return ""

judgementNoContext :: MonadPrint m => JudgementPrinter m
judgementNoContext _ _ = uncurry pprTypeApp
\end{code}

\begin{code}
prettyAllRules :: MonadPrint m =>
                  (TyFamRef -> [Type]) -> Bool
               -> String -> [InfRules] -> m String
prettyAllRules kenv con prefix irss = do
  (js, rss, rs) <- liftM (foldl f (def, def, def)) rules
  return (   rulecmd rs ++ "\n"
          ++ rulescmd rss
          ++ judgecmd js)
    where f (ax, ay, az) (x, y, z) = ( x++braces ax
                                     , y++braces ay
                                     , foldl (flip (++) . braces)
                                       (braces az) z)
          def = "{\\PackageError{twelfppr}{Unknown definition}{}}"
          rules = mapM (prettyRules kenv con) irss
          rulecmd  = newcommand (prefix ++ "rule") 1
          rulescmd = newcommand (prefix ++ "rules") 1
          judgecmd = newcommand (prefix ++ "judgement") 1
\end{code}

\begin{code}
prettyRules :: MonadPrint m => 
               (TyFamRef -> [Type]) -> Bool
            -> InfRules -> m (String, String, [String])
prettyRules kenv con irs@(InfRules kr@(TyFamRef name) _ rules) = do
  rules'   <- mapM procRule rules
  envrules <- if con
              then mapM procVar $ S.toList $ judgeEnv irs
              else return []
  judgem   <- prettyJudgementForm kenv kr
  let allrules = ifbranch
                   (name,
                    judgem ++ "\n" ++
                    intercalate "\n" 
                      (map snd $ envrules ++ rules'))
  let branches = map ifbranch (envrules ++ rules')
  let judgebranch = ifbranch (name, judgem)
  return (judgebranch, allrules, branches)
      where procRule tr'@(TypeRef tn', _) = do
              body <- prettyRule kenv tr'
              return (argescape tn', body)
            procVar kr'@(TyFamRef kn') = do
              body <- prettyVarRule kenv name kr'
              return ( argescape $ "var " ++ name ++ " " ++ kn'
                     , body)
            ifbranch (check, body) =
              ifthenbranch (argescape check) body

prettyRule :: MonadPrint m => 
              (TyFamRef -> [Type])
           -> (TypeRef, InfRule)
           -> m String
prettyRule kenv (TypeRef tn, ir@(InfRule ps con)) = do
  cfgVarMaps (infRuleTypeVars ir)
             (infRuleBoundVars ir)
  asRule tn $ do
    pp   <- asksPrintConf premisePrinter
    ps'  <- mapM (pp kenv) $ reverse ps
    con' <- pprJudgement kenv (S.empty, []) con
    return ("\\frac{\\displaystyle{\n" ++ intercalate "\n\\quad\n" ps' ++
            "}}{\\displaystyle{\n" ++ con' ++ "\n}}")

prettyVarRule :: MonadPrint m => 
                 (TyFamRef -> [Type])
              -> String -> TyFamRef -> m String
prettyVarRule kenv name kr@(TyFamRef kn) = do
  cfgVarMaps (S.fromList $ zip trs ts) S.empty
  asRule rulename $
    pprJudgement kenv (S.empty, [(kr, vs)]) (kr, vs)
      where rulename = name ++ "-" ++ "var" ++ "-" ++ kn
            trs      = map (TypeRef . (:[])) ['a'..]
            vs       = zipWith Var trs ts
            ts       = kenv kr

prettyJudgementForm :: MonadPrint m =>
                       (TyFamRef -> [Type])
                    -> TyFamRef -> m String
prettyJudgementForm kenv kr = do
  cfgVarMaps (S.fromList $ zip trs ts) S.empty
  s <- pprJudgement kenv (S.empty, []) (kr, vs)
  return ("\\fbox" ++ braces ("\\ensuremath{" ++ s ++ "}"))
      where trs = map (TypeRef . (:[])) ['a'..]
            vs  = zipWith Var trs ts
            ts  = kenv kr

asRule :: Monad m => String -> m String -> m String
asRule label body = do
  body' <- body
  return (inEnv "align*" Nothing $
            body' ++ ruleLabel label)

type PremisePrinter m = (TyFamRef -> [Type])
                      -> Judgement -> m String

premiseWithContext :: MonadPrint m => PremisePrinter m
premiseWithContext kenv ((vs, ps), kr, os) =
  bindingVars (map fst $ S.toList vs) $
    pprJudgement kenv (vs, ps) (kr, os)

premiseWithHypoJudgs :: MonadPrint m => PremisePrinter m
premiseWithHypoJudgs kenv ((vs, []), kr, os) = 
  bindingVars (map fst $ S.toList vs) $
    pprJudgement kenv (vs, []) (kr, os)
premiseWithHypoJudgs kenv ((vs, ps), kr, os) =
  bindingVars (map fst $ S.toList vs) $ do
    con <- pprJudgement kenv (vs, []) (kr, os)
    ps'  <- liftM concat $ mapM proc ps
    return $ "{{" ++ ps' ++ "}\\atop" ++ "{\n" ++ con ++ "\n}}"
        where proc p = do p' <- pprJudgement kenv (vs, []) p
                          return ("{\\overline{\\displaystyle{" ++ p' ++
                                  "}}\\atop{\\vdots}}")
\end{code}

\begin{code}
ruleLabel :: String -> String
ruleLabel tn = "\\tag{\\textsc{" ++ texescape tn ++ "}}"
\end{code}

\section{Monad}

\begin{code}
data PrintConf m = PrintConf
  { prettyTypeApp   :: Prettifier TyFamRef m
  , prettyConstApp  :: Prettifier TypeRef m
  , prettyTypeVar   :: TypeVarPrinter m
  , prettyBoundVar   :: TypeVarPrinter m
  , prettyRuleSym   :: SymPrettifier m
  , prettyJudgement :: JudgementPrinter m
  , premisePrinter  :: PremisePrinter m
  , bindings      :: S.Set TypeRef
  }

emptyPrintConf :: MonadPrint m => PrintConf m
emptyPrintConf = PrintConf 
  { prettyTypeApp   = defPrettyTypeApp
  , prettyConstApp  = defPrettyConstApp
  , prettyTypeVar   = defPrettyTypeVar
  , prettyBoundVar   = defPrettyBoundVar
  , prettyRuleSym   = defPrettyRuleSym
  , prettyJudgement = judgementWithContext
  , premisePrinter  = premiseWithContext 
  , bindings        = S.empty
  }

pprJudgement :: MonadPrint m => JudgementPrinter m
pprJudgement kenv x y = do
  pj <- asksPrintConf prettyJudgement
  pj kenv x y

pprTypeApp :: MonadPrint m => Prettifier TyFamRef m
pprTypeApp kr os = do
  pka <- asksPrintConf prettyTypeApp
  pka kr os

pprConstApp :: MonadPrint m => Prettifier TypeRef m
pprConstApp tr os = do
  pta <- asksPrintConf prettyConstApp
  pta tr os
\end{code}

\begin{code}
type NameContext = M.Map TyFamRef (M.Map FreeVarContext TypeRef)

data PrintEnv = PrintEnv 
    { name_context :: NameContext
    , type_vars :: M.Map Type (M.Map TypeRef String)
    , bound_vars :: M.Map Type (M.Map TypeRef String)
    }

emptyPrintEnv :: PrintEnv
emptyPrintEnv = PrintEnv { name_context = M.empty
                         , type_vars    = M.empty
                         , bound_vars   = M.empty }

pprTypeVar :: MonadPrint m => TypeVarPrinter m
pprTypeVar tr ty = do
  bvs <- asksPrintConf bindings
  vm  <- getsPrintEnv (if tr `S.member` bvs
                       then bound_vars else type_vars)
  maybe (error $ "Internal error" ++ show tr ++ " " ++ show ty ++ " "
                   ++ show bvs ++ " " ++ show vm) return $ do
    M.lookup tr =<< M.lookup ty vm
\end{code}

\begin{code}
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
    withPrintConf :: (PrintConf m -> PrintConf m) -> m a -> m a

bindingVar :: MonadPrint m => TypeRef -> m a -> m a
bindingVar tr = withPrintConf (\e ->
  e { bindings = S.insert tr $ bindings e } )

bindingVars :: MonadPrint m => [TypeRef] -> m a -> m a
bindingVars [] m = m
bindingVars (tr:trs) m = bindingVar tr $
  bindingVars trs $ m
\end{code}

\section{Rendering production rules}

\begin{code}
prettyAllProds :: MonadPrint m => Signature
               -> String
               -> [(TyFamUsage, ProdRule)]
               -> m String
prettyAllProds sig prefix prs = do
  branches <- mapM (uncurry $ prettyProd sig) prs
  return $ prodcmd $ foldl (\acc x -> x++braces acc) def branches
      where prodcmd = newcommand (prefix ++ "prod") 1
            def = "{\\PackageError{twelfppr}{Unknown definition}{}}"
\end{code}

\begin{code}
prettyProd :: MonadPrint m => Signature
           -> TyFamUsage
           -> ProdRule
           -> m String
prettyProd sig ku@(kr@(TyFamRef kn), _) prod@(ts, vars) = do
  tvs    <- prodRuleTypeVars sig ku prod
  mvs    <- prodRuleBoundVars sig ku prod
  tr@(TypeRef tn) <- namer sig ku
  let tr' = TypeRef $ "$" ++ tn
  cfgVarMaps tvs mvs
  name   <- pprTypeVar tr (TyName kr)
  terms  <- mapM (prettySymbol sig) ts
  terms' <- if vars
            then liftM (:terms) (bindingVar tr' $
                                   pprTypeVar tr' (TyName kr))
            else return terms
  return (ifthenbranch (argescape kn) $
            "\\begin{tabular}{rl}\n$" ++
            texescape name ++ "$ ::=& $" ++ 
            intercalate "$\\\\ \n $\\mid$ & $" terms' ++
            "$\n" ++ "\\end{tabular}\n")
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
      where prettyPremise ([], ku@(kr, _)) = do
              tr <- namer sig ku
              pprTypeVar tr (TyName kr)
            prettyPremise (kr@(TyFamRef kn):tms, ka) = do
              let tr = TypeRef $ "$" ++ kn
              more <- prettyPremise (tms, ka)
              s    <- bindingVar tr $ pprTypeVar tr (TyName kr)
              return (s ++ "." ++ more)
\end{code}

\begin{code}
namer :: MonadPrint m => Signature -> TyFamUsage -> m TypeRef
namer sig (kr@(TyFamRef kn), vs) = do
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
             | vs == c = TypeRef kn
             | otherwise = TypeRef $ kn ++ replicate n '\''
             where n = 1 + M.size (M.filterWithKey (\k _ -> k/=c) existing)
          c  = initContext kr fd
          fd = fromJust $ M.lookup kr sig
\end{code}


\begin{code}
prodRuleTypeVars :: MonadPrint m => Signature
                 -> TyFamUsage
                 -> ProdRule 
                 -> m (S.Set (TypeRef, Type))
prodRuleTypeVars sig ku@(kr, _) (syms, _) = do
  s <- liftM (S.fromList . concat) (mapM symvars syms)
  tr <- namer sig ku
  return $ S.insert (tr, TyName kr) s
    where symvars (_, ps) =
            forM ps $ \(_, ku'@(kr', _)) -> do
              tr <- namer sig ku'
              return (tr, TyName kr')

prodRuleBoundVars :: MonadPrint m => Signature
                 -> TyFamUsage
                 -> ProdRule
                 -> m (S.Set (TypeRef, Type))
prodRuleBoundVars sig _ (syms, _) = do
  liftM (mconcat . concat) (mapM symvars syms)
    where symvars (_, ps) = do
            liftM mconcat (mapM (mapM f . fst) ps)
          f kr' = do
            TypeRef tn <- namer sig (kr', c)
            return $ S.singleton ( TypeRef $ "$" ++ tn
                                 , TyName kr')
                where c = initContext kr' $
                          fromJust $ M.lookup kr' sig
\end{code}
