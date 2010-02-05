%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Reconstruct
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\begin{ignore}
\begin{code}
{-# LANGUAGE PackageImports, GeneralizedNewtypeDeriving #-}
\end{code}
\end{ignore}

\chapter{TwelfPPR.Reconstruct}
\label{chap:twelfppr.reconstruct}

In this module we implement term reconstruction of Twelf terms.  We do
not actually implement the reconstruction algorithm, but merely use
the |TwelfPPR.TwelfServer| module to dispatch to an instance of the
real Twelf implementation.  The crux to making this work is the
undocumented |readDecl| Twelf server protocol command which is also
used by Twelf's own Emacs interface.

\begin{code}
module TwelfPPR.Reconstruct ( reconstruct
) where

import Control.Applicative

import Control.Monad.Trans

import TwelfPPR.Parser
import TwelfPPR.TwelfServer
\end{code}

The |readDecl| command is simple: it reads a declaration (terminated
with a dot, as all declarations) and outputs some result.  As
mentioned above, the command is not documented, but for term and
abbreviation definitions, the result will the comparable fully
type-expanded definition.

\begin{code}
reconstructDecl :: MonadIO m => Decl -> TwelfMonadT m Decl
reconstructDecl d = (either (error . show) fst . parse) <$> cmd
    where parse = parseDecl initDeclState "stdin"
          cmd   = runTwelfCmd $ "readDecl\n" ++ show d ++ "\n"
\end{code}

It rarely makes sense to reconstruct a term by itself, as they will
undoubtedly rely on type definitions.  Rather, it is more useful to
process an entire program, as a sequence of declarations, and produce
a resulting list of declarations, each type-expanded if necessary.  We
only pass term and abbreviation definitions to the |readDecl| command,
as it makes no sense to reconstruct the others.

\begin{code}
reconstruct :: MonadIO m => String -> [Decl] -> m [Decl]
reconstruct bin = withTwelfServer bin . mapM reconstruct'
    where reconstruct' :: MonadIO m => Decl -> TwelfMonadT m Decl
          reconstruct' d@(DTerm _ _)         = reconstructDecl d
          reconstruct' d@(DDefinition _ _ _) = reconstructDecl d
          reconstruct' d                     = return d
\end{code}
