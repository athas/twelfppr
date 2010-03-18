%----------------------------------------------------------------------------
%--
%-- Module      :  LF
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-- Maintainer  :  athas@sigkill.dk
%-- Stability   :  unstable
%-- Portability :  not portable, uses mtl, posix
%--
%-- A tool for prettyprinting Twelf signatures.
%--
%-----------------------------------------------------------------------------

\chapter{LF representation}
\label{chap:lf representation}

This chapter implements the data types and ancillary functions for
representing LF in Haskell.

\begin{code}
module TwelfPPR.LF ( TyFamRef(..)
                   , TypeRef(..)
                   , Type(..)
                   , conclusion
                   , premises
                   , Object(..)
                   , Kind(..)
                   , TyFamDef(..)
                   , defElems
                   , Signature
                   , freeInType
                   , freeInObj
                   , renameType
                   , renameObj
                   , referencedTyFams
                   , objFreeVars
                   , objBoundVars )
    where

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
\end{code}

The full LF type theory is defined by the following grammar.
\\
\begin{tabular}{lrcl}
TyFams & $K$ & ::= & $\text{type} \mid \Pi x:A.K$ \\
Families & $A$ & ::= & $a \mid A\ M \mid \Pi x:A_1.A_2$ \\
Objects & $M$ & ::= & $c \mid x \mid \lambda x:A. M \mid M_1\ M_2$ \\
Signatures & $\Sigma$ & ::= & $\cdot \mid \Sigma, a:K \mid \Sigma,
c:A$ \\
Contexts & $\Gamma$ & ::= & $\cdot \mid \Gamma, x:A$
\end{tabular}
\\

We ignore contexts, they do not matter for our purposes.  A $c$ is the
name of a constant, and an $x$ is the name of a type variable.  An $a$
is the name of a type family.  This leads us to the following
definition of types.  We define disjunct types for naming families and
constants for increased type safety.

\begin{code}
newtype TyFamRef = TyFamRef String
    deriving (Show, Eq, Ord)
newtype TypeRef = TypeRef String
    deriving (Show, Eq, Ord)

data Type = TyCon  (Maybe TypeRef) Type Type
          | TyApp  Type Object
          | TyName TyFamRef
            deriving (Show, Eq, Ord)
\end{code}

A type $\Pi x_1 : A_1. \Pi x_2 : A_2.\ldots \Pi x_{n-1} : A_{n-1}.A_n$
is said to have the \textit{premises} $A_1, A_2 \ldots A_{n-1}$ and
the \textit{conclusion} $A_n$.  This is a bit of a stretch, as this
terminology is usually reserved for cases when $x_i$ is not free in
the enclosed term, but useful none the less.

\begin{code}
conclusion :: Type -> Type
conclusion (TyCon _ _ t2) = conclusion t2
conclusion t              = t

premises :: Type -> [Type]
premises (TyCon _ t1 t2) = t1 : premises t2
premises _               = []
\end{code}

LF |Object|s should always be in $\beta$ and $\eta$ normal form,
though that restriction is not enforced by this definition.  We
distinguish between referencing types that are part of some top-level
constant definition in the signature (the |Const| constructor) and
those that are type variables in the enclosing term (|Var|).  We
annotate all variables with their type, at both binding- and
usage-points.

\begin{code}
data Object = Const TypeRef
            | Var TypeRef Type
            | Lambda TypeRef Type Object
            | App Object Object
              deriving (Show, Ord)
\end{code}

When comparing objects for equality, we permit $\alpha$-conversion of
variables.

\begin{code}
instance Eq Object where
    Const tr == Const tr' = tr == tr'
    Var tr1 t1 == Var tr2 t2 = tr1 == tr2 && t1 == t2
    Lambda tr1 t1 o1 == Lambda tr2 t2 o2 =
      o1 == renameObj tr2 tr1 o2 && t1 == t2
    App o1a o1b == App o2a o2b =
      o1a == o2a && o1b == o2b
    _ == _ = False
\end{code}

Kind are simple, consisting either of a $\Pi$ constructor or the
\texttt{type} atom.

\begin{code}
data Kind = KiType
          | KiCon (Maybe TypeRef) Type Kind
            deriving (Show, Eq)
\end{code}

A type family definition maps type names to the actual types (or
specifically, type families) themselves.

\begin{code}
data TyFamDef = TyFamDef Kind [(TypeRef, Type)]
                   deriving (Show, Eq)

defElems :: TyFamDef -> [Type]
defElems (TyFamDef _ l) = map snd l
\end{code}

A signature is a map of names of type family names to type
family definitions.

\begin{code}
type Signature = M.Map TyFamRef TyFamDef
\end{code}

\section{Operations on LF terms}

We will eventually need to extract various interesting nuggets of
information about LF definitions.  In particular, whether a given
variable is free in a type or object will be of interest to many
transformations.

\begin{code}
freeInType :: TypeRef -> Type -> Bool
freeInType tr (TyCon (Just tr') t1 t2) =
    (tr /= tr' && freeInType tr t2)
    || freeInType tr t1
freeInType tr (TyCon Nothing t1 t2) =
    (freeInType tr t2) || freeInType tr t1
freeInType tr (TyApp t o) = freeInType tr t || freeInObj tr o
freeInType _ _ = False

freeInObj :: TypeRef -> Object -> Bool
freeInObj tr (Const tr') = tr == tr'
freeInObj tr (Var tr' _) = tr == tr'
freeInObj tr (Lambda tr' t o) =
     (tr /= tr' && freeInObj tr o)
     || freeInType tr t
freeInObj tr (App o1 o2) = freeInObj tr o1 || freeInObj tr o2
\end{code}

The meaning of an LF term is independent of how its type variables are
named (that is, $\alpha$-conversion is permitted).  Therefore, we can
define functions that rename variables.

\begin{code}
renameType :: TypeRef -> TypeRef -> Type -> Type
renameType from to = r
    where r (TyCon Nothing t1 t2) = 
            TyCon Nothing (r t1) (r t2)
          r (TyCon (Just tr) t1 t2)
            | tr == from = TyCon (Just tr) t1 t2
            | otherwise  = TyCon (Just tr) (r t1) (r t2)
          r (TyApp t o) = TyApp (r t) (renameObj from to o)
          r t = t 

renameObj :: TypeRef -> TypeRef -> Object -> Object
renameObj from to = r
    where r (Const tr) = Const (var tr)
          r (Var tr t) = Var (var tr) (renameType from to t)
          r (Lambda tr t o)
              | tr == from = Lambda tr t' o
              | otherwise  = Lambda tr t' (r o)
              where t' = renameType from to t
          r (App o1 o2) = App (r o1) (r o2)
          var tr | tr == from = to
                 | otherwise  = tr
\end{code}

To determine which kinds are applied in some type $t$ we
can trivially walk through the tree.

\begin{code}
refsInType :: Type -> S.Set TyFamRef
refsInType (TyCon _ t1 t2) = refsInType t1 `S.union` refsInType t2
refsInType (TyApp t _)     = refsInType t
refsInType (TyName k)      = S.singleton k
\end{code}

The kind applications of some type family definition is the union of
all kind applications in the member types.

\begin{code}
refsInTyFam :: TyFamDef -> S.Set TyFamRef
refsInTyFam kd = 
  foldl S.union S.empty $ map refsInType $ defElems kd
\end{code}

The above definitions only catch immediate references, which will not
be adequate for our purposes.  Thus, we also need to recursively
inspect the referenced kinds.

\begin{code}
referencedTyFams :: Signature -> TyFamRef -> S.Set TyFamRef
referencedTyFams sig = referencedTyFams' S.empty
    where referencedTyFams' visited fr
              | fr `S.member` visited = S.empty
              | otherwise = foldl S.union (S.singleton fr) refs'
              where refs' = map (referencedTyFams' visited') refs
                    refs  = S.toList $ refsInTyFam $ fromJust $ M.lookup fr sig
                    visited' = S.insert fr visited
\end{code}

The set of type variables, bound or free, of an object is defined by
simple recursive equations.  Note that this will interact badly with
shadowing, $\alpha$-conversions should be performed to ensure
uniqueness of all type variables prior to using this function.

\begin{code}
objFreeVars :: Object -> S.Set (TypeRef, Type)
objFreeVars (Var tr t) = S.singleton (tr, t)
objFreeVars (Lambda tr t o) =
  (tr, t) `S.delete` objFreeVars o
objFreeVars (App o1 o2) =
  objFreeVars o1 `S.union` objFreeVars o2
objFreeVars _ = S.empty

objBoundVars :: Object -> S.Set (TypeRef, Type)
objBoundVars (Lambda tr t o) =
  S.singleton (tr, t) `S.union` objBoundVars o
objBoundVars (App o1 o2) =
  objBoundVars o1 `S.union` objBoundVars o2
objBoundVars _ = S.empty
\end{code}
