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

import qualified Data.Set as S

import TwelfPPR.LF
\end{code}

\begin{code}
prettyObject :: Object -> String
prettyObject = pretty S.empty

pretty :: S.Set TypeRef -> Object -> String
pretty _ (Type (TypeRef tn)) = tn
pretty s (Lambda tr@(TypeRef tn) o) =
  "\\" ++ tn ++ "." ++ pretty (S.insert tr s) o
pretty s (App o1 (Type tr@(TypeRef tn)))
  | tr `S.member` s = pretty s o1 ++ "[" ++ tn ++ "]"
pretty s (App o1 o2@(App _ _)) =
  pretty s o1 ++ "(" ++ pretty s o2 ++ ")"
pretty s (App o1 o2) =
  pretty s o1 ++ " " ++ pretty s o2
\end{code}
