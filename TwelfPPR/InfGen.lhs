%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.InfGen
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\chapter{|TwelfPPR.InfGen|}

In Twelf, we represent judgements as types, with a given type
corresponding to an inference rule in traditional notation.  This
module implements the transformation of a subset of Twelf types to a
simple abstract form of inference rules.

\begin{code}
module TwelfPPR.InfGen ( Judgement(..)
                       , InfRule(..)
                       , Premise
                       , Conclusion
                       , pprAsJudgement
                       ) where

import qualified Data.Map as M
import qualified Data.Set as S

import TwelfPPR.LF
\end{code}

We define an inference rule to consist of a set of \textit{premises},
with each premise corresponding to an LF type of kind \texttt{*} (that
is, no arrows), and a single \textit{conclusion}, also corresponding
to an LF type.  Note that this simple model does not include the
concept of an ``environment'' in which judgements are made, putting a
heavy restriction on the kinds of LF types we can represent as
inference rules.

A type family maps to a single \textit{judgement definition}, which
maps names of types in the family to inference rules.  An inference
rule consists of a potentially empty set of premises (actually a list,
as we wish to preserve the order in which the programmer originally
specified the premises in the Twelf code) and a conclusion, both of
which are simply the name of some kind applied to a potentially empty
sequence of objects.  The kind in the conclusion will always be the
same kind as the judgement definition describes, as that would be the
original criteria for inclusion.

\begin{code}
data Judgement = Judgement KindRef (M.Map TypeRef InfRule)
data InfRule = InfRule [Premise] Conclusion
type Premise = (HOPremise, KindRef, [Object])
type HOPremise = (S.Set TypeRef, [(KindRef, [Object])])
type Conclusion = (KindRef, [Object])
\end{code}

Given the name of a kind and its definition, we can produce the above
abstract representation of a judgement by mapping each type in
the kind to its corresponding inference rule.

\begin{code}
pprAsJudgement :: (KindRef, KindDef) -> Judgement
pprAsJudgement (kr, KindDef ms) = 
  Judgement kr $ M.map pprAsRule ms
\end{code}

\begin{code}
pprAsRule :: Type -> InfRule
pprAsRule (TyCon (Just _) _ t2) = pprAsRule t2
pprAsRule (TyCon Nothing t1 t2) =
  InfRule (pprAsPremise t1 : ps) c
      where InfRule ps c = pprAsRule t2
pprAsRule t = InfRule [] $ pprAsConclusion t
\end{code}

\begin{code}
pprAsConclusion :: Type -> Conclusion
pprAsConclusion t = ppr t []
    where ppr (TyKind kr) os = (kr, os)
          ppr (TyApp t' o) os = ppr t' (o:os)
          ppr _ _ = error "Type constructor found unexpectedly in term"
\end{code}

\begin{code}
pprAsPremise :: Type -> Premise
pprAsPremise t = ppr t S.empty []
    where ppr (TyCon Nothing t1 t2) es ps = ppr t2 es (ppr' t1 []:ps)
          ppr (TyCon (Just kr) _ t2) es ps =
            ppr t2 (kr `S.insert` es) ps
          ppr t1 es ps = ((es, ps), kr, os)
              where (kr, os) = ppr' t1 []
          ppr' (TyKind kr) os = (kr, os)
          ppr' (TyApp t1 o) os = ppr' t1 (o:os)
          ppr' _ _ = error "Type constructor found unexpectedly in term"
\end{code}
