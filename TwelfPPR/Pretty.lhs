%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Pretty
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.Pretty|}

This module defines primitives for printing Twelf terms by themselves.

\begin{code}
module TwelfPPR.Pretty ( prettyObject ) where

import Data.List

import TwelfPPR.LF
\end{code}

\begin{code}
prettyObject :: Object -> String
prettyObject = pretty

pretty :: Object -> String
pretty (Const (TypeRef tn)) = tn
pretty (Var (TypeRef tn))   = tn
pretty (Lambda (TypeRef tn) o) =
  "\\" ++ tn ++ "." ++ pretty o
pretty (App o1 o2) = descend o1 [o2]
  where descend (Var (TypeRef tn)) args =
          tn ++ "[" ++ intercalate "][" (map pretty args) ++ "]"
        descend (Const (TypeRef tn)) args =
          tn ++ " " ++ intercalate " " (map pretty args)
        descend (App o1' o2') args = descend o1' $ o2' : args
        descend o args =
          pretty o ++ " " ++ intercalate " " (map pretty args)
\end{code}
