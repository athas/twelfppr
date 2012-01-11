%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.LaTeX
%-- Copyright   :  (c) Troels Henriksen 2010
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.LaTeX|}
\label{chap:twelfppr.latex}

Primitives for making it easier to generate LaTeX.

\begin{code}
module TwelfPPR.LaTeX ( texescape
                      , argescape
                      , newcommand
                      , ifthenbranch
                      , inEnv
                      , brackets
                      , braces )
    where
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

\begin{code}
argescape :: String -> String
argescape "" = ""
argescape ('\\':ss) = "\\backslash " ++ argescape ss
argescape ('{':ss)  = "\\{" ++ argescape ss
argescape ('}':ss)  = "\\}" ++ argescape ss
argescape (s:ss)    = s : argescape ss
\end{code}

\begin{code}
wrap :: String -> String -> String -> String
wrap s e b = s ++ b ++ e

brackets :: String -> String
brackets = wrap "[" "]"

braces :: String -> String
braces = wrap "{" "}"
\end{code}

\begin{code}
inEnv :: String -> Maybe String -> String -> String
inEnv n a b =    "\\begin" ++ braces n
              ++ maybe "" brackets a ++ "\n"
              ++ b ++ "\n"
              ++ "\\end" ++ braces n ++ "\n"
\end{code}

\begin{code}
newcommand :: String -> Integer -> String -> String
newcommand n a b =    "\\newcommand" 
                   ++ braces ('\\' : n)
                   ++ brackets (show a)
                   ++ braces b ++ "\n"
\end{code}

\begin{code}
ifthenbranch :: String -> String -> String
ifthenbranch x b =
  "\\ifthenelse" ++
  braces ("\\equal{#1}" ++ braces x) ++
  braces b
\end{code}
