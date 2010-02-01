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
module TwelfPPR.LF ( KindRef
                   , TypeRef
                   , Type(..)
                   , conclusion
                   , premises
                   , Object(..)
                   , FamilyDef(..)
                   , Signature
                   , referencedKinds )
    where
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
\end{code}

A type $t_1 \rightarrow t_2 \ldots t_n$ is said to have the
\textit{premises} $t_1, t_2 \ldots t_{n-1}$ and the
\textit{conclusion} $t_n$.

\begin{code}
type KindRef = String
type TypeRef = String

data Type = TyArrow Type Type
          | TyCon String Type Type
          | TyApp KindRef [Object]
            deriving (Show, Eq)

conclusion :: Type -> String
conclusion (TyArrow _ t2) = conclusion t2
conclusion (TyCon _ _ t2) = conclusion t2
conclusion (TyApp t _)    = t

premises :: Type -> [Type]
premises (TyArrow t1 t2) = t1 : premises t2
premises (TyCon _ t1 t2) = t1 : premises t2
premises _               = []
\end{code}

|Object|s are a simple subset of full Twelf objects.  They are closed,
in $\beta$ normal form, and fully constructed. 

\begin{code}
data Object = Type TypeRef
            | Var TypeRef
            | Lambda TypeRef Object
            | App Object Object
              deriving (Show, Eq)
\end{code}

A type family definition maps names of terms of the premises to the
actual terms themselves.

\begin{code}
data FamilyDef = FamilyDef (M.Map TypeRef Type)
                   deriving (Show, Eq)
\end{code}

A Twelf signature is a map of names of type families to type family
definitions.

\begin{code}
type Signature = M.Map String FamilyDef
\end{code}

\section{Inspecting for information}

We will eventually need to extract various interesting nuggets of
information about LF definitions.

To determine which kinds are applied in some type $t$ we
can trivially walk through the tree.

\begin{code}
refsInType :: Type -> S.Set KindRef
refsInType (TyArrow t1 t2) = refsInType t1 `S.union` refsInType t2
refsInType (TyCon _ t1 t2) = refsInType t1 `S.union` refsInType t2
refsInType (TyApp k _)     = S.singleton k
\end{code}

The kind applications of some type family definition is the union of
all kind applications in the member types.

\begin{code}
refsInTyFam :: FamilyDef -> S.Set KindRef
refsInTyFam (FamilyDef fam) = 
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
