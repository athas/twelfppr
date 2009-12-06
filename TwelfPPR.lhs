%----------------------------------------------------------------------------
%--
%-- Module      :  Main
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

\documentclass[oldfontcommands]{memoir}
%include polycode.fmt
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[british]{babel}
\let\fref\undefined
\let\Fref\undefined
\usepackage{fancyref}
\usepackage{hyperref}
\usepackage{url}
\renewcommand{\ttdefault}{txtt}
\renewcommand{\rmdefault}{ugm}

\author{Troels Henriksen (athas@@sigkill.dk)}

\title{TwelfPPR: Prettyprinting Twelf signatures}

% The following macro is useful for hiding code blocks from LaTeX (but
% not GHC).
\long\def\ignore#1{}

\begin{document}

\maketitle

\begin{code}
module Main (main) where
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
\end{code}

|Term|s are a simple subset of full Twelf terms.  They are closed, in
$\beta$ normal form, and fully constructed.  A term $t_1 \rightarrow
t_2 \ldots t_n$ is said to have the \textit{premises} $t_1, t_2 \ldots
t_{n-1}$ and the \textit{conclusion} $t_n$.

\begin{code}
data Term = Fam String
          | Arrow Term Term
            deriving (Show, Eq)

conclusion :: Term -> String
conclusion (Fam t) = t
conclusion (Arrow _ t2) = conclusion t2

premises :: Term -> [Term]
premises (Fam _) = []
premises (Arrow t1 t2) = t1 : premises t2
\end{code}

A type family definition maps names of terms of the premises to the
actual terms themselves.

\begin{code}
data FamilyDef = FamilyDef (M.Map String Term)
                   deriving (Show, Eq)
\end{code}

A Twelf signature is a map of names of type families to type family
definitions.

\begin{code}
type Signature = M.Map String FamilyDef
\end{code}

Prettyprinting a signature consists of prettyprinting each type family
definition, along with the terms in that family, as a grammar,
separating each type family with a newline.

\begin{code}
ppr :: Signature -> String
ppr sig = newlines $ pprdefs $ M.toList sig
    where newlines = intercalate "\n"
          pprdefs  = map (pprAsGrammar sig)
\end{code}

A single type family definition is printed as a production rule, with
the symbols on the right-hand side being a function not only of the
terms in the type family, but also of whether any terms in the family
are used in higher-order premises in any term in the signature.

\begin{code}
pprAsGrammar :: Signature -> (String, FamilyDef) -> String
pprAsGrammar sig (name, FamilyDef ms) = 
    pprFam name .
    mappend (famVars sig name) .
    mconcat .
    map termSymbols .
    M.toList $ ms

pprFam :: String -> S.Set String -> String
pprFam name ts = capitalise name ++ 
                 " ::= " ++
                 intercalate " | " (S.toList ts)
\end{code}

A term without premises is printed as its capitalised name, otherwise
it is printed as its name applied to a tuple containing its premises.

\begin{code}
capitalise :: String -> String
capitalise "" = ""
capitalise (c:s) = toUpper c : s

termSymbols :: (String, Term) -> S.Set String
termSymbols (name, Fam _) = S.singleton $ capitalise name
termSymbols (name, t) =
    S.singleton (capitalise name ++ "(" ++ args ++ ")")
    where args = intercalate "," . map prettyPremise . premises $ t
\end{code}

A constant premise is its capitalised name, just like a constant term.
A parametric premise $p_1 \rightarrow p_2 \rightarrow \ldots
\rightarrow p_n$ is printed as $\$p_1.\$p_2.\ldots \$p_{n-1}.p_n$.

\begin{code}
prettyPremise :: Term -> String
prettyPremise (Fam s) = capitalise s
prettyPremise (Arrow (Fam t) t2) = 
    "$" ++ capitalise t ++ "." ++ prettyPremise t2
prettyPremise _ = fail "Cannot handle greater than 2nd order HOAS"
\end{code}

With HOAS in Twelf we can write terms where formal parameters are
implicit, but in production rules we want such things to be explicit.
For each parametric premise we create a symbol for variables of the
type families used as parameters in the premise.  I am not convinced
that there is a point to multiple symbols for variables just because
they differ in their LF type.

\begin{code}
famVars :: Signature -> String -> S.Set String
famVars sig name =
    S.fromList . mconcat . concatMap (varsFromFam . snd) . M.toList $ sig
    where varsFromFam (FamilyDef defs) =
              map (varsFromTermDef name . snd) . M.toList $ defs

varsFromTermDef :: String -> Term -> [String]
varsFromTermDef _ (Fam _) = []
varsFromTermDef name t = concatMap varsFromPremise $ premises t
    where varsFromPremise p
              | conclusion p == name = varsOf p
              | otherwise            = []
          varsOf (Fam _) = []
          varsOf (Arrow (Fam t1) t2) = ("x/" ++ capitalise t1) : varsOf t2
          varsOf _ = fail "Cannot handle greater than 2nd order HOAS"
\end{code}

Below are sample |Signature| values.

\begin{code}
sample1 = M.fromList
          [("tm", FamilyDef $ M.fromList 
                    [ ("empty", Fam "tm")
                    , ("app", Arrow (Fam "tm") 
                                (Arrow (Fam "tm") (Fam "tm")))
                    , ("lam", Arrow (Arrow (Fam "tm") (Fam "tm"))
                                (Arrow (Fam "tm") (Fam "tm")))
                    ])
          ]
\end{code}

Prettyprinted as:

\begin{verbatim}
Tm ::= App(Tm,Tm) | Empty | Lam($Tm.Tm,Tm) | x/Tm
\end{verbatim}

\begin{code}
sample2 = M.fromList
          [ ("tp", FamilyDef $ M.fromList
                     [ ("arrow", Arrow (Fam "tp") 
                                  (Arrow (Fam "tp") (Fam "tp")))
                     , ("unit", Fam "tp")
                     ])
          , ("tm", FamilyDef $ M.fromList 
                    [ ("empty", Fam "tm")
                    , ("app", Arrow (Fam "tm") 
                                (Arrow (Fam "tm") (Fam "tm")))
                    , ("lam", Arrow (Arrow (Fam "tm") (Arrow (Fam "tp") (Fam "tm")))
                                (Fam "tm"))
                    ])
          ]
\end{code}

Prettyprinted as:

\begin{verbatim}
Tm ::= App(Tm,Tm) | Empty | Lam($Tm.$Tp.Tm) | x/Tm | x/Tp
Tp ::= Arrow(Tp,Tp) | Unit
\end{verbatim}

\begin{code}
sample3 = M.fromList
          [ ("foo", FamilyDef $ M.fromList
                      [ ("foo_a", Fam "foo")
                      , ("foo_b", Arrow (Fam "foo") (Fam "foo"))
                      ])
          , ("bar", FamilyDef $ M.fromList
                      [ ("bar_a", Fam "bar")
                      , ("bar_b", Arrow (Arrow (Fam "bar") 
                                                   (Fam "foo"))
                         (Fam "bar")) 
                      ])
          ]
\end{code}

\begin{verbatim}
Bar ::= Bar_a | Bar_b($Bar.Foo)
Foo ::= Foo_a | Foo_b(Foo) | x/Bar
\end{verbatim}

\begin{ignore}
\begin{code}
main :: IO ()
main = mapM_ putStrLn $ map ppr [sample3]
\end{code}
\end{ignore}

\end{document}
