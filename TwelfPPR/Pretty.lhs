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
import TwelfPPR.LF
\end{code}

\begin{code}
prettyObject :: Object -> String
prettyObject (Type (TypeRef s)) = s
prettyObject (Var (TypeRef s))  = s
prettyObject (Lambda (TypeRef t) o) = "\\" ++ t ++ "." ++ prettyObject o
prettyObject (App o1 o2@(App _ _)) = 
    prettyObject o1 ++ " (" ++ prettyObject o2 ++ ")"
prettyObject (App o1 o2) = prettyObject o1 ++ " " ++ prettyObject o2
\end{code}
