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
                       , prettyAllGrmRules
                       , prettyAllAbbrs
                       , PrintConf(..)
                       , emptyPrintConf
                       , ProdPrettifier
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
                       , defPrettyProd
                       , pprVar
                       , pprObject
                       , texVar
                       , texConst
                       , prettyName
                       , prettyGrammar
                       , namer
                       , prettyRules
                       , premiseWithContext
                       , judgementWithContext
                       , judgementNoContext
                       , premiseWithHypoJudgs
                       , splitVar )
    where

import Control.Arrow
import Control.Monad.Reader

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
       -> S.Set (VarRef, Type)
       -> m (M.Map Type (M.Map VarRef String))
varMap p s = do
  procVars p $ S.toList s

splitVar :: VarRef -> (String, Maybe Integer, Int)
splitVar (VarRef tn) =
  case matchRegex r tn of
    Just [name, "", ps] -> (name, Nothing, length ps)
    Just [name, i, ps]  -> (name, Just $ read i, length ps)
    _                   -> (tn, Nothing, 0)
    where r = mkRegex "([^0-9']+)([0-9]*)('*)"

procVars :: MonadPrint m =>
            m (TypeVarPrinter m)
         -> [(VarRef, Type)]
         -> m (M.Map Type (M.Map VarRef String))
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
        -> [(VarRef, Type)]
        -> S.Set String
        -> m [(Type, (VarRef, String))]
uniqify _ [] _ = return []
uniqify p ((tr, ty):ts) seen = do
  s <- realUniq p (tr, ty) seen
  more <- uniqify p ts $ s `S.insert` seen
  return $ (ty, (tr, s)):more

realUniq :: MonadPrint m =>
            TypeVarPrinter m
         -> (VarRef, Type)
         -> S.Set String
         -> m String
realUniq p (tr, ty) seen = do
  s <- p tr ty
  case (s `S.member` seen) of
    True  -> realUniq p (tr', ty) seen
    False -> return s
    where (name, idx, ps) = splitVar tr
          tr' = VarRef (name ++
                        show idx' ++
                        replicate ps '\'')
          idx' = maybe 1 (1+) idx

cfgVarMaps :: MonadPrint m => 
             S.Set (VarRef, Type)
          -> S.Set (VarRef, Type) -> m ()
cfgVarMaps ts ms = do
  vm <- varMap (asksPrintConf prettyTypeVar) ts
  mm <- varMap (asksPrintConf prettyBoundVar) ms
  modifyPrintEnv $ \e -> e { type_vars = vm
                           , bound_vars = mm }

withVarMaps :: MonadPrint m =>
               S.Set (VarRef, Type)
            -> S.Set (VarRef, Type)
            -> m a -> m a
withVarMaps ts ms m = do
  pe <- getPrintEnv
  cfgVarMaps ts ms
  val <- m
  putPrintEnv pe
  return val
\end{code}

\section{Generalities}

\begin{code}
type ProdPrettifier m =
    Signature -> (ConstRef, Production) -> m String
type Prettifier o m = o -> [Object] -> m String
\end{code}

\begin{code}
texConst :: String -> String
texConst s = "\\textrm{" ++ texescape s ++ "}"

texVar :: String -> String
texVar s = texescape name ++
              maybe "" (\i -> "_{" ++ show i ++ "}") index ++
              replicate primes '\''
    where (name, index, primes) = splitVar $ VarRef s
\end{code}

\begin{code}
defPrettyTypeApp :: MonadPrint m => Prettifier TyFamRef m
defPrettyTypeApp (TyFamRef kn) [] = return $ texConst kn
defPrettyTypeApp (TyFamRef kn) os = do
  args <- mapM pprObject os
  return $ texConst kn ++ "(" ++ intercalate ", " args ++ ")"

defPrettyConstApp :: MonadPrint m => Prettifier ConstRef m
defPrettyConstApp (ConstRef tn) [] = return $ texConst tn
defPrettyConstApp (ConstRef tn) os = do
  args <- mapM pprObject os
  return $ texConst tn ++ "(" ++ intercalate ", " args  ++ ")"

type TypeVarPrinter m = VarRef -> Type -> m String

defPrettyTypeVar :: MonadPrint m => TypeVarPrinter m
defPrettyTypeVar (VarRef tn) _ = return $ texVar tn

defPrettyBoundVar :: MonadPrint m => TypeVarPrinter m
defPrettyBoundVar (VarRef tn) _ = return $ texVar $ "$" ++ tn
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
  pprVar tr ty
pprObject (Lambda tr ty o) = bindingVar tr $ do
  body <- pprObject o
  vs <- pprVar tr ty
  return $ vs ++ "." ++ body
pprObject (App o1 o2) = descend o1 [o2]
  where descend (Var tr ty) os = do
          args <- mapM pprObject os
          s    <- pprVar tr ty
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
      where procRule tr'@(ConstRef tn', _) = do
              body <- prettyRule kenv tr'
              return (argescape tn', body)
            procVar kr'@(TyFamRef kn') = do
              body <- pprVarRule kenv name kr'
              return ( argescape $ "var " ++ name ++ " " ++ kn'
                     , body)
            ifbranch (check, body) =
              ifthenbranch (argescape check) body

prettyRule :: MonadPrint m => 
              (TyFamRef -> [Type])
           -> (ConstRef, InfRule)
           -> m String
prettyRule kenv (ConstRef tn, ir@(InfRule ps con)) = do
  cfgVarMaps (infRuleGlobalVars ir)
             (infRuleBoundVars ir)
  asRule tn $ do
    pp   <- asksPrintConf premisePrinter
    ps'  <- mapM (pp kenv) $ reverse ps
    con' <- pprJudgement kenv (S.empty, []) con
    return ("\\frac{\\displaystyle{\n" ++ intercalate "\n\\quad\n" ps' ++
            "}}{\\displaystyle{\n" ++ con' ++ "\n}}")

pprVarRule :: MonadPrint m => 
              (TyFamRef -> [Type])
           -> String -> TyFamRef -> m String
pprVarRule kenv name kr@(TyFamRef kn) = do
  cfgVarMaps (S.fromList $ zip trs ts) S.empty
  asRule rulename $
    pprJudgement kenv (S.empty, [(kr, vs)]) (kr, vs)
      where rulename = name ++ "-" ++ "var" ++ "-" ++ kn
            trs      = map (VarRef . (:[])) ['a'..]
            vs       = zipWith Var trs ts
            ts       = kenv kr

prettyJudgementForm :: MonadPrint m =>
                       (TyFamRef -> [Type])
                    -> TyFamRef -> m String
prettyJudgementForm kenv kr = do
  cfgVarMaps (S.fromList $ zip trs ts) S.empty
  s <- pprJudgement kenv (S.empty, []) (kr, vs)
  return ("\\fbox" ++ braces ("\\ensuremath{" ++ s ++ "}"))
      where trs = map (VarRef . (:[])) ['a'..]
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
  , prettyConstApp  :: Prettifier ConstRef m
  , prettyTypeVar   :: TypeVarPrinter m
  , prettyBoundVar  :: TypeVarPrinter m
  , prettyProd      :: ProdPrettifier m
  , prettyJudgement :: JudgementPrinter m
  , premisePrinter  :: PremisePrinter m
  , bindings        :: S.Set VarRef
  }

emptyPrintConf :: MonadPrint m => PrintConf m
emptyPrintConf = PrintConf 
  { prettyTypeApp   = defPrettyTypeApp
  , prettyConstApp  = defPrettyConstApp
  , prettyTypeVar   = defPrettyTypeVar
  , prettyBoundVar  = defPrettyBoundVar
  , prettyProd      = defPrettyProd
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

pprConstApp :: MonadPrint m => Prettifier ConstRef m
pprConstApp tr os = do
  pta <- asksPrintConf prettyConstApp
  pta tr os
\end{code}

\begin{code}
type NameContext = M.Map TyFamRef (M.Map FreeVarContext VarRef)

data PrintEnv = PrintEnv 
    { name_context :: NameContext
    , type_vars :: M.Map Type (M.Map VarRef String)
    , bound_vars :: M.Map Type (M.Map VarRef String)
    }

emptyPrintEnv :: PrintEnv
emptyPrintEnv = PrintEnv { name_context = M.empty
                         , type_vars    = M.empty
                         , bound_vars   = M.empty }

pprVar :: MonadPrint m => TypeVarPrinter m
pprVar tr ty = do
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

bindingVar :: MonadPrint m => VarRef -> m a -> m a
bindingVar tr = withPrintConf (\e ->
  e { bindings = S.insert tr $ bindings e } )

bindingVars :: MonadPrint m => [VarRef] -> m a -> m a
bindingVars [] m = m
bindingVars (tr:trs) m = bindingVar tr $
  bindingVars trs $ m
\end{code}

\section{Rendering production rules}

\begin{code}
prettyAllGrmRules :: MonadPrint m => Signature
                  -> String
                  -> [(TyFamUsage, GrammarRule)]
                  -> m String
prettyAllGrmRules sig prefix prs = do
  prodbody <- liftM (foldl f def)
                $ mapM (uncurry $ prettyGrammar sig) prs
  return $ prodcmd prodbody
    where f ax x  = ( x++braces ax )
          prodcmd = cmdf "grammar"
          cmdf s  = newcommand (prefix ++ s) 1
          def = "{\\PackageError{twelfppr}{Unknown definition}{}}"
\end{code}

\begin{code}
prettyGrammar :: MonadPrint m => Signature
              -> TyFamUsage
              -> GrammarRule
              -> m String
prettyGrammar sig ku@(kr@(TyFamRef kn), _) prod@(ts, vars) = do
  tvs    <- prodRuleTypeVars sig ku prod
  mvs    <- prodRuleBoundVars sig ku prod
  tr@(VarRef tn) <- namer sig ku
  let tr' = VarRef tn
  cfgVarMaps tvs mvs
  name   <- pprVar tr (TyName kr)
  terms  <- mapM (pprProd sig) ts
  terms' <- if vars
            then liftM (:terms) (bindingVar tr' $
                                   pprVar tr' (TyName kr))
            else return terms
  let prodbody = ifthenbranch (argescape kn) $
                   "\\begin{tabular}{rl}\n$" ++
                   texescape name ++ "$ ::=& $" ++ 
                   intercalate "$\\\\ \n $\\mid$ & $" terms' ++
                 "$\n" ++ "\\end{tabular}\n"
  return prodbody
\end{code}

\begin{code}
pprProd :: MonadPrint m => Signature 
        -> (ConstRef, Production)
        -> m String
pprProd sig (tr, ts) = do
  prs <- asksPrintConf prettyProd
  prs sig (tr, ts)
\end{code}

\begin{code}
namer :: MonadPrint m => Signature -> TyFamUsage -> m VarRef
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
             | vs == c = VarRef kn
             | otherwise = VarRef $ kn ++ replicate n '\''
             where n = 1 + M.size (M.filterWithKey (\k _ -> k/=c) existing)
          c  = initContext kr fd
          fd = fromJust $ M.lookup kr sig
\end{code}


\begin{code}
prodRuleTypeVars :: MonadPrint m => Signature
                 -> TyFamUsage
                 -> GrammarRule 
                 -> m (S.Set (VarRef, Type))
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
                 -> GrammarRule
                 -> m (S.Set (VarRef, Type))
prodRuleBoundVars sig _ (syms, _) = do
  liftM (mconcat . concat) (mapM symvars syms)
    where symvars (_, ps) = do
            liftM mconcat (mapM (mapM f . fst) ps)
          f kr' = do
            VarRef tn <- namer sig (kr', c)
            return $ S.singleton ( VarRef tn
                                 , TyName kr')
                where c = initContext kr' $
                          fromJust $ M.lookup kr' sig
\end{code}

\section{Abbreviations}

\begin{code}
prettyAllAbbrs :: MonadPrint m => String
               -> [(TyFamRef, [(ConstRef, Type, Object)])]
               -> m String
prettyAllAbbrs prefix tfs = do
  (derivsbody, derivbody) <-
      liftM (foldl f (def, def))
                $ mapM (uncurry $ prettyAbbrs) tfs
  return $ intercalate "\n" [ derivscmd derivsbody
                            , derivcmd derivbody ]
    where f (ax, ay) (x, y) = ( x++braces ax
                              , foldl (flip (++) . braces)
                                (braces ay) y)
          derivcmd  = cmdf "deriv"
          derivscmd = cmdf "derivs"
          cmdf s = newcommand (prefix ++ s) 1
          def = "{\\PackageError{twelfppr}{Unknown definition}{}}"
\end{code}

\begin{code}
prettyAbbrs :: MonadPrint m => TyFamRef 
            -> [(ConstRef, Type, Object)]
            -> m (String, [String])
prettyAbbrs (TyFamRef tn) abbrs = do
  abbrs' <- mapM procAbbr abbrs
  let derivbranches = map (ifbranch . second wrapalign) abbrs'
      derivsbody    = ifbranch $ second wrapalign $
                        (tn, intercalate "\n"
                               (map snd abbrs'))
  return (derivsbody, derivbranches)
    where procAbbr (cr@(ConstRef cn), _, o) = do
            abbr' <- prettyAbbr (cr, o)
            return (cn, abbr')
          ifbranch (check, body) =
            ifthenbranch (argescape check) body
          wrapalign = inEnv "align*" Nothing
\end{code}

\begin{code}
prettyAbbr :: MonadPrint m => (ConstRef, Object) -> m String
prettyAbbr (cr, o) = do
  let (o2, gvs, lvs, os) = abbrArgs cr o
      lvs' = lvs `S.union` objBoundVars o2
  withVarMaps gvs lvs' $ do
    bindingVars (map fst $ S.toList lvs) $ do
      lhs <- pprConstApp cr os
      rhs <- pprObject o2
      return (lhs ++ "&\\triangleq&" ++ rhs ++ "\\\\")
\end{code}

\begin{code}
abbrArgs :: ConstRef
         -> Object
         -> ( Object
            , S.Set (VarRef, Type)
            , S.Set (VarRef, Type)
            , [Object])
abbrArgs (ConstRef cn) o =
  let tvcs = map (VarRef . (:[])) ['a'..]
      (ro, gvs, bvs, os) = split o tvcs
  in (ro, S.fromList gvs, S.fromList bvs, os)
    where split (Lambda vr ty@(TyName _) o') vcs =
              let (ro, gvs, bvs, os) = split o' (filter (/=vr) vcs)
              in  (ro, (vr, ty):gvs, bvs, Var vr ty:os)
          split (Lambda vr ty o') vcs =
            let (v, vcs') = extract ty vcs []
                (ro, gvs, bvs, os) = split o' (filter (/=vr) vcs')
                vars = map (uncurry Var) v
            in ( ro
               , (vr, ty) : gvs
               , v ++ bvs
               , vars ++ (foldl App (Var vr ty) vars : os) )
          split o' _ = (o', [], [], [])
          extract (TyName _) vcs r = (reverse r, vcs)
          extract (TyCon Nothing ty1 ty2) (vc:vcs) r =
            extract ty2 vcs ((vc, ty1):r)
          extract _ _ _ = error $ "Cannot handle abbreviation " ++ cn

defPrettyProd :: MonadPrint m => ProdPrettifier m
defPrettyProd _ (ConstRef tn, []) =
  return $ prettyName tn
defPrettyProd sig (ConstRef tn, ts) = do
  args <- liftM (intercalate ", ") $ mapM prettyPremise ts
  return $ prettyName tn ++ "(" ++ args ++ ")"
      where prettyPremise ([], ku@(kr, _)) = do
              tr <- namer sig ku
              pprVar tr (TyName kr)
            prettyPremise (kr@(TyFamRef kn):tms, ka) = do
              let tr = VarRef $ kn
              more <- prettyPremise (tms, ka)
              s    <- bindingVar tr $ pprVar tr (TyName kr)
              return (s ++ "." ++ more)
\end{code}
