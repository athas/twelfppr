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
                   , Signature)
    where
import qualified Data.Map as M
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
data FamilyDef = FamilyDef (M.Map String Type)
                   deriving (Show, Eq)
\end{code}

A Twelf signature is a map of names of type families to type family
definitions.

\begin{code}
type Signature = M.Map String FamilyDef
\end{code}
