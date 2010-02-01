%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.GrammarGen
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.GrammarGen|}

This chapter implements prettyprinting Twelf definitions as production
rules in a grammar.  Not all type definitions can be printed in this
way, but for those that can, it is far more readable than inference
rules.

\begin{ignore}
\begin{code}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, PackageImports #-}
\end{code}
\end{ignore}

\begin{code}
module TwelfPPR.GrammarGen ( GGenEnv(..)
                           , emptyGGenEnv
                           , MonadGGen(..)
                           , prodRulePossible
                           , pprAsProd
                           , pprFam
) where
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S

import TwelfPPR.LF
import TwelfPPR.Pretty
import TwelfPPR.Util
\end{code}

\begin{code}
type FreeVarContext = S.Set KindRef
type TyUsage = (TypeRef, FreeVarContext)
type NameContext = M.Map TypeRef (M.Map FreeVarContext String)
data GGenEnv = GGenEnv { name_context :: NameContext
                       , prod_rules   :: M.Map String (S.Set String) }

emptyGGenEnv :: GGenEnv
emptyGGenEnv = GGenEnv { name_context = M.empty
                       , prod_rules   = M.empty }

class Monad m => MonadGGen m where
    getGGenEnv :: m GGenEnv
    putGGenEnv :: GGenEnv -> m ()

    getsGGenEnv :: (GGenEnv -> a) -> m a
    getsGGenEnv f = getGGenEnv >>= \s -> return (f s)

    modifyGGenEnv :: (GGenEnv -> GGenEnv) -> m ()
    modifyGGenEnv f = getGGenEnv >>= \s ->
                            putGGenEnv (f s)

instance MonadState GGenEnv m => MonadGGen m where
    getGGenEnv = get
    putGGenEnv = put
\end{code}

A type is printable as a production rule if its conclusion is a 0-arity kind.

\begin{code}
prodRulePossible :: FamilyDef -> Bool
prodRulePossible (FamilyDef ms) = all (check . snd) $ M.toList ms
    where check (TyArrow _ t)       = check t
          check (TyApp _ [])        = True
          check _                   = False
\end{code}

A single type family definition is printed as a production rule, with
the symbols on the right-hand side being a function not only of the
terms in the type family, but also of whether any terms in the family
are used in higher-order premises in any term in the signature.

\begin{code}
pprAsProd :: MonadGGen m => Signature
          -> (TypeRef, FamilyDef)
          -> m ()
pprAsProd sig x@(t, _) = pprWithContext sig context x
    where context = initContext sig t

pprWithContext :: MonadGGen m => Signature
               -> FreeVarContext
               -> (TypeRef, FamilyDef)
               -> m ()
pprWithContext sig c (t, FamilyDef ms) = do
  prods <- getsGGenEnv prod_rules
  name  <- namer sig (t, c)
  case M.lookup name prods of
    Just _  -> return ()
    Nothing -> do syms <- mapM (typeSymbols (namer sig) c) $ M.toList ms
                  modifyGGenEnv $ \s ->
                      s { prod_rules = M.insert name (mappend varsyms . mconcat $ syms)
                                       (prod_rules s) }
      where vars    = initContext sig t `S.intersection` c
            varsyms = S.map (('$':) . capitalise) vars

pprFam :: String -> S.Set String -> String
pprFam name ts = capitalise name ++ 
                 " ::= " ++
                 intercalate " | " (S.toList ts)
\end{code}

\begin{code}
namer :: MonadGGen m => Signature -> TyUsage -> m String
namer sig (t, vs') = do
  context <- getsGGenEnv name_context
  case M.lookup t context of
    Just m  -> case M.lookup vs m of
                 Just n -> return n
                 Nothing -> do
                   let new = newName m
                   modifyGGenEnv $ \s ->
                     s { name_context =
                         M.insert t (M.insert vs new m) context }
                   pprWithContext sig vs (t, fromJust $ M.lookup t sig)
                   return new
    Nothing -> do
      let new = newName M.empty
      modifyGGenEnv $ \s ->
          s { name_context =
              M.insert t (M.singleton vs new) context }
      pprWithContext sig vs (t, fromJust $ M.lookup t sig)
      return new
    where newName :: M.Map FreeVarContext String -> String
          newName existing
             | vs == initContext sig t = t
             | otherwise = t ++ replicate n '\''
             where n = 1 + M.size (M.filterWithKey (\k _ -> k/=eps) existing)
          vs = vs' `S.intersection` referencedKinds sig t
          eps = S.singleton t
\end{code}

A term without premises is printed as its capitalised name, otherwise
it is printed as its name applied to a tuple containing its premises.

\begin{code}
typeSymbols :: Monad m => (TyUsage -> m String)
            -> FreeVarContext
            -> (String, Type)
            -> m (S.Set String)
typeSymbols _ _ (name, TyApp _ []) = return $ S.singleton $ capitalise name
typeSymbols nf c (name, t) = do
  liftM f $ liftM (intercalate ",") $ mapM (prettyPremise nf c) $ premises t
      where f args = S.singleton (capitalise name ++ "(" ++ args ++ ")")
\end{code}

A constant premise is its capitalised name, just like a constant type.
A parametric premise $p_1 \rightarrow p_2 \rightarrow \ldots
\rightarrow p_n$ is printed as $\$p_1.\$p_2.\ldots \$p_{n-1}.p_n$.

\begin{code}
prettyPremise :: Monad m =>
                 (TyUsage -> m String)
              -> FreeVarContext
              -> Type 
              -> m String
prettyPremise nf c (TyArrow (TyApp t []) t2) = do
    s <- prettyPremise nf (S.insert t c) t2
    return $ "$" ++ capitalise t ++ "." ++ s
prettyPremise _  _ (TyArrow _ _)  = fail "Cannot handle greater than 2nd order HOAS"
prettyPremise nf c (TyCon _ _ t2) = prettyPremise nf c t2  -- checkme
prettyPremise nf c (TyApp s [])   = liftM capitalise $ nf (s, c)
prettyPremise nf c (TyApp k os)   = liftM (f . capitalise) $ nf (k, c)
    where f op = op ++ "(" ++ args ++ ")"
          args = intercalate "," . map prettyObject $ os
\end{code}

With HOAS in Twelf we can write types where formal parameters are
implicit, but in production rules we want such things to be explicit.
For each parametric premise we create a symbol for variables of the
type families used as parameters in the premise.

\begin{code}
hasVar :: TypeRef -> FamilyDef -> Bool
hasVar k (FamilyDef fam) = any (typeHasVar) $ M.elems fam
    where typeHasVar    = any premiseHasVar . premises 
          premiseHasVar = isJust . find (==TyApp k []) . premises

initContext :: Signature -> String -> FreeVarContext
initContext sig name 
    | hasVar name (fromJust $ M.lookup name sig) = S.singleton name
    | otherwise = S.empty
\end{code}
