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
                           , KindUsage
                           , ProdRule
                           , RuleSymbol
                           , prodRulePossible
                           , pprAsProd
                           , pprWithContext
                           , prettyProd
) where
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S

import TwelfPPR.LF
import TwelfPPR.Pretty
import TwelfPPR.Util
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
type FreeVarContext = S.Set KindRef
type KindUsage = (KindRef, FreeVarContext)
type ProdRule = (M.Map TypeRef RuleSymbol, Bool)
type RuleSymbol = [([KindRef], KindUsage)]
\end{code}

\begin{code}
type NameContext = M.Map KindRef (M.Map FreeVarContext String)
data GGenEnv = GGenEnv 
    { name_context :: NameContext
    , prod_rules   :: M.Map KindUsage ProdRule
    }

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
prodRulePossible (FamilyDef ms) = all check $ M.elems ms
    where check (TyArrow _ t)       = check t
          check (TyApp _ [])        = True
          check _                   = False
\end{code}

A single kind definition is printed as a production rule, with the
symbols on the right-hand side being a function of the member types.
We ensure that when we generate a production rule, all referenced
kinds (taking into account the possibility of free variables) are also
generated.

\begin{code}
pprAsProd :: MonadGGen m => Signature
          -> (KindRef, FamilyDef)
          -> m ()
pprAsProd sig x@(kr, fd) = do
  let prod = pprWithContext c x
  modifyGGenEnv $ \s ->
      s { prod_rules = M.insert (kr, c) prod (prod_rules s) }
  ensureProds sig prod
    where c = initContext kr fd
\end{code}

\begin{code}
ensureProds :: MonadGGen m => Signature
            -> ProdRule
            -> m ()
ensureProds sig (syms, _) =
  forM_ (krs syms) $ \(kr, c) -> do
    let c' = c `S.intersection` referencedKinds sig kr
    prods <- getsGGenEnv prod_rules
    case M.lookup (kr, c') prods of
      Just _ -> return ()
      Nothing -> do
        let prod = pprWithContext c' (kr, fd)
            fd = fromJust $ M.lookup kr sig
        modifyGGenEnv $ \s ->
          s { prod_rules = M.insert (kr, c') prod (prod_rules s) }
        ensureProds sig prod
    where krs = concat . map (map snd) . M.elems

pprWithContext :: FreeVarContext
               -> (KindRef, FamilyDef)
               -> ProdRule
pprWithContext c (kr, FamilyDef ms) = 
  (syms, kr `S.member` c && (hasVar kr $ FamilyDef ms))
    where syms = M.map (typeSymbol c) ms
\end{code}

\begin{code}
prettyProd :: MonadGGen m => Signature
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
prettySymbol :: MonadGGen m => Signature
             -> (TypeRef, RuleSymbol)
             -> m String
prettySymbol _ (TypeRef tn, []) = return $ capitalise tn
prettySymbol sig (TypeRef tn, ts) = do
  args <- liftM (intercalate ", ") $ mapM prettyPremise ts
  return $ capitalise tn ++ "(" ++ args ++ ")"
      where prettyPremise :: MonadGGen m => ([KindRef], KindUsage) 
                          -> m String
            prettyPremise ([], ku) = do
              name <- namer sig ku
              return $ capitalise name
            prettyPremise (KindRef kn:tms, ku) = do
              more <- prettyPremise (tms, ku)
              return (("$" ++ capitalise kn ++ ".") ++ more)
\end{code}

\begin{code}
namer :: MonadGGen m => Signature -> KindUsage -> m String
namer sig (kr@(KindRef kn), vs) = do
  context <- getsGGenEnv name_context
  case M.lookup kr context of
    Just m  -> case M.lookup vs m of
                 Just n -> return n
                 Nothing -> do
                   let new = newName m
                   modifyGGenEnv $ \s ->
                     s { name_context =
                         M.insert kr (M.insert vs new m) context }
                   return new
    Nothing -> do
      let new = newName M.empty
      modifyGGenEnv $ \s ->
          s { name_context =
              M.insert kr (M.singleton vs new) context }
      return new
    where newName existing
             | vs == init = capitalise kn
             | otherwise = capitalise kn ++ replicate n '\''
             where n = 1 + M.size (M.filterWithKey (\k _ -> k/=init) existing)
          init = initContext kr fd
          fd  = fromJust $ M.lookup kr sig
\end{code}

A term without premises is printed as its capitalised name, otherwise
it is printed as its name applied to a tuple containing its premises.

\begin{code}
typeSymbol :: FreeVarContext
           -> Type
           -> RuleSymbol
typeSymbol _ (TyApp _ []) = []
typeSymbol c t = map (handlePremise c) $ premises t

handlePremise :: FreeVarContext
              -> Type 
              -> ([KindRef], KindUsage)
handlePremise c (TyArrow (TyApp kr []) t2) = (kr : krs, ku)
    where (krs, ku) = handlePremise (S.insert kr c) t2
handlePremise _ (TyArrow _ _)  = error "Cannot handle greater than 2nd order HOAS"
handlePremise c (TyCon _ _ t2) = handlePremise c t2  -- checkme
handlePremise c (TyApp kr [])   = 
  ([], (kr, c))
handlePremise c (TyApp k os)   = undefined
\end{code}

A constant premise is its capitalised name, just like a constant type.
A parametric premise $p_1 \rightarrow p_2 \rightarrow \ldots
\rightarrow p_n$ is printed as $\$p_1.\$p_2.\ldots \$p_{n-1}.p_n$.

With HOAS in Twelf we can write types where formal parameters are
implicit, but in production rules we want such things to be explicit.
For each parametric premise we create a symbol for variables of the
type families used as parameters in the premise.

\begin{code}
hasVar :: KindRef -> FamilyDef -> Bool
hasVar kr (FamilyDef fam) = any (typeHasVar) $ M.elems fam
    where typeHasVar    = any premiseHasVar . premises 
          premiseHasVar = isJust . find (==TyApp kr []) . premises

initContext :: KindRef -> FamilyDef -> FreeVarContext
initContext kr fd
    | hasVar kr fd = S.singleton kr
    | otherwise = S.empty
\end{code}
