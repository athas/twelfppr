%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Util
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.Util|}

This appendix contains miscellaneous utility definitions that are not
specialised to the purpose of the program.

\begin{code}
module TwelfPPR.Util ( capitalise
                     , texescape ) where
import Data.Char
\end{code}

The |capitalise| function capitalises the first element of its argument.

\begin{code}
capitalise :: String -> String
capitalise "" = ""
capitalise (c:s) = toUpper c : s
\end{code}

\begin{code}
texescape :: String -> String
texescape "" = ""
texescape ('_':ss) = "\\_" ++ texescape ss
texescape ('#':ss) = "\\#" ++ texescape ss
texescape ('$':ss) = "\\$" ++ texescape ss
texescape ('&':ss) = "\\&" ++ texescape ss
texescape ('>':ss) = "$>$" ++ texescape ss
texescape ('<':ss) = "$<$" ++ texescape ss
texescape (s:ss)   = s : texescape ss
\end{code}
