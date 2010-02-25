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
                           , FreeVarContext
                           , KindUsage
                           , ProdRule
                           , RuleSymbol
                           , Contexter
                           , defaultContexter
                           , simpleContexter
                           , prodRulePossible
                           , pprAsProd
                           , pprWithContext
                           , initContext )
    where

import Control.Monad.State
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S

import TwelfPPR.LF
\end{code}

Consider the following simple Twelf signature.

\begin{verbatim}
foo : type.
bar : type.
baz : type.

foo_a : foo.
foo_b : bar -> foo.

bar_a : bar.
bar_b : (bar -> foo) -> bar.

baz_a : bar -> baz.
\end{verbatim}

A naive way to represent this as a grammar would be as follows.
\\
\begin{tabular}{rl}
  $Foo ::=$ & $Foo\_a \mid Foo\_b(Bar)$ \\
  $Bar ::=$ & $\$Bar \mid Bar \mid Bar\_b(\$Bar.Foo)$ \\
  $Baz ::=$ & $Baz\_a(Bar)$ \\
\end{tabular}
\\
This representation ignores the fact that, in the Twelf code, a
$\$Bar$ (variable) cannot appear when the $Bar$ rule is reached
through a $Foo\_b$ or $Baz\_a$ nonterminal (except if a $Foo\_b$ is
reached through a $Bar\_b$).  A grammar that accurately represents the
meaning of the original code would be as follows:
\\
\begin{tabular}{rl}
  $Foo ::=$ & $Foo\_a \mid Foo\_b(Bar')$ \\
  $Foo' ::=$ & $Foo\_a \mid Foo\_b(Bar)$ \\
  $Bar ::=$ & $\$Bar \mid Bar \mid Bar\_b(\$Bar.Foo')$ \\
  $Bar' ::=$ & $Bar \mid Bar\_b(\$Bar.Foo')$ \\
  $Baz ::=$ & $Baz\_a(Bar')$ \\
\end{tabular}
\\

This means that we not only have to track which kinds are referenced
in the type definitions, but also which kinds can appear as free
variables in subterms.

\begin{code}
type ProdRule = (M.Map TypeRef RuleSymbol, Bool)
type RuleSymbol = [([KindRef], KindUsage)]
type KindUsage = (KindRef, FreeVarContext)
type FreeVarContext = S.Set KindRef

type Contexter =  KindRef
               -> FreeVarContext
               -> FreeVarContext

defaultContexter :: Signature -> Contexter
defaultContexter sig kr c =
  c `S.intersection` referencedKinds sig kr
simpleContexter :: Signature -> Contexter
simpleContexter sig kr _ =
  initContext kr (fromJust $ M.lookup kr sig)
\end{code}

\begin{code}
data GGenEnv = GGenEnv 
    { prod_rules   :: M.Map KindUsage ProdRule
    }

emptyGGenEnv :: GGenEnv
emptyGGenEnv = GGenEnv { 
                 prod_rules= M.empty
               }

class Monad m => MonadGGen m where
    getGGenEnv :: m GGenEnv
    putGGenEnv :: GGenEnv -> m ()

    getsGGenEnv :: (GGenEnv -> a) -> m a
    getsGGenEnv f = getGGenEnv >>= \s -> return (f s)

    modifyGGenEnv :: (GGenEnv -> GGenEnv) -> m ()
    modifyGGenEnv f = getGGenEnv >>= \s ->
                            putGGenEnv (f s)
\end{code}

A type is printable as a production rule if its conclusion and
premises are constant.

\begin{code}
prodRulePossible :: KindDef -> Bool
prodRulePossible (KindDef ms) = all check $ M.elems ms
    where check (TyCon _ _ t)       = check t
          check (TyKind _)          = True
          check _                   = False
\end{code}

A single kind definition is printed as a production rule, with the
symbols on the right-hand side being a function of the member types.
We ensure that when we generate a production rule, all referenced
kinds (taking into account the possibility of free variables) are also
generated.

\begin{code}
pprAsProd :: MonadGGen m => Signature
          -> Contexter
          -> (KindRef, KindDef)
          -> m ()
pprAsProd sig con x@(kr, fd) = do
  let prod = pprWithContext con c x
  modifyGGenEnv $ \s ->
      s { prod_rules = M.insert (kr, c) prod (prod_rules s) }
  ensureProds sig con prod
    where c = initContext kr fd
\end{code}

\begin{code}
ensureProds :: MonadGGen m => Signature
            -> Contexter
            -> ProdRule
            -> m ()
ensureProds sig con (syms, _) =
  forM_ (krs syms) $ \(kr, c) -> do
    let c' = con kr c
    prods <- getsGGenEnv prod_rules
    case M.lookup (kr, c') prods of
      Just _ -> return ()
      Nothing -> do
        let prod = pprWithContext con c' (kr, fd)
            fd   = fromJust $ M.lookup kr sig
        modifyGGenEnv $ \s ->
          s { prod_rules = M.insert (kr, c') prod (prod_rules s) }
        ensureProds sig con prod
    where krs = concat . map (map snd) . M.elems

pprWithContext :: Contexter
               -> FreeVarContext
               -> (KindRef, KindDef)
               -> ProdRule
pprWithContext con c (kr, KindDef ms) = 
  (syms, kr `S.member` c && (hasVar kr $ KindDef ms))
    where syms = M.map (typeSymbol con c) ms
\end{code}

A term without premises is printed as its capitalised name, otherwise
it is printed as its name applied to a tuple containing its premises.

\begin{code}
typeSymbol :: Contexter
           -> FreeVarContext
           -> Type
           -> RuleSymbol
typeSymbol _ _ (TyKind _) = []
typeSymbol con c t = map (handlePremise con c) $ premises t

handlePremise :: Contexter
              -> FreeVarContext
              -> Type 
              -> ([KindRef], KindUsage)
handlePremise con c (TyCon _ (TyKind kr) t2) = (kr : krs, ku)
    where (krs, ku) = handlePremise con (S.insert kr c) t2
handlePremise _ _ (TyCon _ _ _)  = error "Cannot handle greater than 2nd order HOAS"
handlePremise con c (TyKind kr)    = ([], (kr, con kr c))
handlePremise _ _ (TyApp _ _)    =
  error "Cannot handle premises with arity > 0"
\end{code}

A constant premise is its capitalised name, just like a constant type.
A parametric premise $p_1 \rightarrow p_2 \rightarrow \ldots
\rightarrow p_n$ is printed as $\$p_1.\$p_2.\ldots \$p_{n-1}.p_n$.

With HOAS in Twelf we can write types where formal parameters are
implicit, but in production rules we want such things to be explicit.
For each parametric premise we create a symbol for variables of the
type families used as parameters in the premise.

\begin{code}
hasVar :: KindRef -> KindDef -> Bool
hasVar kr (KindDef fam) = any (typeHasVar) $ M.elems fam
    where typeHasVar    = any premiseHasVar . premises 
          premiseHasVar = isJust . find (==TyKind kr) . premises

initContext :: KindRef -> KindDef -> FreeVarContext
initContext kr fd
    | hasVar kr fd = S.singleton kr
    | otherwise = S.empty
\end{code}
