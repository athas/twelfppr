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
module TwelfPPR.LF ( KindRef(..)
                   , TypeRef(..)
                   , Type(..)
                   , conclusion
                   , premises
                   , Object(..)
                   , KindDef(..)
                   , Signature
                   , referencedKinds )
    where
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
\end{code}

The full LF type theory is defined by the following grammar.
\\
\begin{tabular}{lrcl}
Kinds & $K$ & ::= & $\text{type} \mid \Pi x:A.K$ \\
Families & $A$ & ::= & $a \mid A\ M \mid \Pi x:A_1.A_2$ \\
Objects & $M$ & ::= & $c \mid x \mid \lambda x:A. M \mid M_1\ M_2$ \\
Signatures & $\Sigma$ & ::= & $\cdot \mid \Sigma, a:K \mid \Sigma, c:A$
Contexts & $\Gamma$ & ::= $\cdot \mid \Gamma, x:A$
\end{tabular}
\\

We ignore contexts, they do not matter for our purposes.  A $c$ is the
name of a type constant, and an $x$ is the name of a type variable.
An $a$ is the name of a kind.  This leads us to the following
definition of types.

\begin{code}
newtype KindRef = KindRef String
    deriving (Show, Eq, Ord)
newtype TypeRef = TypeRef String
    deriving (Show, Eq, Ord)

data Type = TyCon (Maybe String) Type Type
          | TyApp Type Object
          | TyKind KindRef
            deriving (Show, Eq)
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

LF |Object|s should always be in $\beta$ normal form, though that
restriction is not enforced by this definition.  We distinguish
between referencing types that are part of some top-level constant
definition in the signature (the |Const| constructor) and those that
are type variables in the enclosing term (|Var|).

\begin{code}
data Object = Const TypeRef
            | Var TypeRef
            | Lambda TypeRef Object
            | App Object Object
              deriving (Show, Eq)
\end{code}

A kind definition maps type names to the actual types (or
specifically, type families) themselves.

\begin{code}
data KindDef = KindDef (M.Map TypeRef Type)
                   deriving (Show, Eq)
\end{code}

A Twelf signature is a map of names of kind names to kind definitions.

\begin{code}
type Signature = M.Map KindRef KindDef
\end{code}

\section{Inspecting signatures}

We will eventually need to extract various interesting nuggets of
information about LF definitions.

To determine which kinds are applied in some type $t$ we
can trivially walk through the tree.

\begin{code}
refsInType :: Type -> S.Set KindRef
refsInType (TyCon _ t1 t2) = refsInType t1 `S.union` refsInType t2
refsInType (TyApp t _)     = refsInType t
refsInType (TyKind k)      = S.singleton k
\end{code}

The kind applications of some type family definition is the union of
all kind applications in the member types.

\begin{code}
refsInTyFam :: KindDef -> S.Set KindRef
refsInTyFam (KindDef fam) = 
  foldl S.union S.empty $ map refsInType $ M.elems fam
\end{code}

The above definitions only catch immediate references, which will not
be adequate for our purposes.  Thus, we also need to recursively
inspect the referenced kinds.

\begin{code}
referencedKinds :: Signature -> KindRef -> S.Set KindRef
referencedKinds sig = referencedKinds' S.empty
    where referencedKinds' visited fr
              | fr `S.member` visited = S.empty
              | otherwise = foldl S.union (S.singleton fr) refs'
              where refs' = map (referencedKinds' visited') refs
                    refs  = S.toList $ refsInTyFam $ fromJust $ M.lookup fr sig
                    visited' = S.insert fr visited
\end{code}
