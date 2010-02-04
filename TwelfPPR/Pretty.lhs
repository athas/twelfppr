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
import qualified Data.Set as S

import TwelfPPR.LF
import TwelfPPR.Parser(upcaseId)
\end{code}

\begin{code}
prettyObject :: Object -> String
prettyObject = pretty

pretty :: Object -> String
pretty (Type (TypeRef tn)) = tn
pretty (Lambda (TypeRef tn) o) =
  "\\" ++ tn ++ "." ++ pretty o
pretty (App o1 o2) = descend o1 [o2]
  where descend (Type (TypeRef tn)) args
          | upcaseId tn =
              tn ++ "[" ++ intercalate "][" (map pretty args) ++ "]"
          | otherwise =
              tn ++ " " ++ intercalate " " (map pretty args)
        descend (App o1 o2) args = descend o1 $ o2 : args
        descend o args =
          pretty o ++ " " ++ intercalate " " (map pretty args)
pretty (App o1 o2@(App _ _)) =
  pretty o1 ++ "(" ++ pretty o2 ++ ")"
pretty (App o1 o2) =
  pretty o1 ++ " " ++ pretty o2
\end{code}
