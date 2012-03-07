%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Parser
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\begin{ignore}
\begin{code}
{-# LANGUAGE PackageImports, FlexibleInstances #-}
\end{code}
\end{ignore}

\chapter{|TwelfPPR.Parser|}

This chapter implements a parser for the Twelf implementation of the
ELF programming language.  The entire language is supported, including
all syntactical shortcuts and conveniences provided by Twelf.

The parser is constructed through the Parsec library of parser
combinators, with additional combinators from the Parco library.  This
may cost performance, compared to using a traditional parser
generator, but not to a degree significant for our uses, especially
considering the relatively small size of normal Twelf programs.

\begin{code}
module TwelfPPR.Parser ( upcaseId
                       , idChar
                       , Term(..)
                       , Decl(..)
                       , DeclState(..)
                       , initDeclState
                       , parseDecl
                       , parseSig
                       , parseConfig
                       , toSignature
) where

import Control.Applicative
import "mtl" Control.Monad.Identity

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Ord

import Text.Parsec hiding ((<|>), many, optional, token)
import Text.Parsec.String
import qualified Text.Parco
import Text.Parco.Expr

import qualified TwelfPPR.LF as LF
\end{code}

To begin with, we define a data structure for terms.  Twelf does not
syntactically distinguish between the levels in LF type theory, and
neither do we, at this level.

\begin{code}
data Term = TType
          | TArrow Term Term
          | TSchem (String, Term) Term
          | TLambda (String, Term) Term
          | TApp Term Term
          | TAscription Term Term
          | THole
          | TVar String
          | TConstant String
            deriving (Eq)
\end{code}

\section{Lexing}

According to the Twelf grammar, identifiers consist of sequences of
printable non-reserved, non-whitespace characters.

\begin{code}
idReserved :: String
idReserved = ":.()[]{}%\""

idChar :: GenParser Char u Char
idChar = satisfy $ \c -> and [ c `notElem` idReserved
                             , not $ isSpace c
                             , isPrint c]
\end{code}

An uppercase identifier is one that begins with an underscore or a
letter in the range 'A'---'Z'.  A lowercase identifier begins with any
other non-reserved character.  Hence, we can distinguish between
uppercase-- and lowercase--identifiers solely by their first
character.  Identifiers consisting solely of an underscore are treated
specially, as they represent a missing part of the program to be
created through term reconstruction.

\begin{code}
upcaseId :: String -> Bool
upcaseId []      = True
upcaseId ('_':_) = True
upcaseId (c:_)   = c `elem` ['A'..'Z']

ident :: String -> Term
ident "_"              = THole
ident s | upcaseId s   = TVar s
        | otherwise    = TConstant s
\end{code}

Much of the parsing process consists of combining syntactical tokens
(lexemes), while ignoring whitespace, comments and the like.  The
Twelf grammar does not truly specify rules for whitespace and
comments, but we opt for a rather conventional approach where it is
permitted as separators between tokens in all cases.  There is no
lexical distinction between operators and "identifiers", as the
programmer can define arbitrary constants as infix and postfix
operators.  This makes it seem alluring to use Parsec's own lexer
generator facility, but there is a catch: In Twelf, line comments are
initiated with \texttt{"\% "} or \texttt{"\%\%"}, but the
|TokenParser| data structure in Parsec only permits a single syntax
for line comments.  We could define comments to start with merely a
single percentage sign, but that would cause two new problems: For
one, we would also skip many Twelf declarations (such as
\texttt{\%infix}), and we would also conflict with Twelf block
comments, which are begun with \texttt{"\%\{"}.  Due to a Parsec
implementation detail, line comments are preferred to block comments,
and we would thus end with the latter interpreted as the former.  As
an additional detail, we also consider a percentage sign followed by a
newline character to be a line comment, as this construct seems to be
semi-common in actual Twelf code.  It is therefore necessary that we
define our own lexer.  Fortunately, this is not very hard in Parsec.

To begin with, we handle whitespace as defined by the lexical
conventions in the Twelf User's Guide.  Note that is includes line-
and block-comments as well.

\begin{code}
whiteSpace :: GenParser Char u ()
whiteSpace = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
    where oneLineComment = do _ <- try (    try (char '%' *> many1 linespaces)
                                        <|> try (string "%%")
                                        <|> string "%" <* lookAhead newline)
                              skipMany (satisfy (/= '\n'))
          multiLineComment = try (string "%{") *> inCommentMulti
          inCommentMulti =     try (string "}%") *> return ()
                           <|> multiLineComment *> inCommentMulti
                           <|> skipMany1 (noneOf startEnd) *> inCommentMulti
                           <|> oneOf startEnd *> inCommentMulti
                           <?> "end of comment"
              where startEnd = nub ("}%" ++ "%{")
          simpleSpace = skipMany1 (linespaces <|> char '\n')
          linespaces  = oneOf " \t\r\v\f"
\end{code}

The following definitions all
discard trailing whitespace and comments, thereby assuming that there
is no leading whitespace.

\begin{code}
lexeme     :: GenParser Char u a -> GenParser Char u a
lexeme p   = p <* whiteSpace
symbol     :: String -> GenParser Char u String
symbol     = lexeme . string
identifier :: GenParser Char u String
identifier = lexeme (many1 idChar) <?> "identifier"
token      :: String -> GenParser Char u String
token k    = lexeme (try $ string k <* notFollowedBy idChar)
             <?> "token '"++k++"'"
parens     :: GenParser Char u a -> GenParser Char u a
parens     = between (symbol "(") (symbol ")")
brackets   :: GenParser Char u a -> GenParser Char u a
brackets   = between (symbol "[") (symbol "]")
braces     :: GenParser Char u a -> GenParser Char u a
braces     = between (symbol "{") (symbol "}")
decimal    :: GenParser Char u Integer
decimal    = lexeme $ do digits <- many1 digit
                         let n = foldl (\x d -> 10*x + toInteger (digitToInt d)) 0 digits
                         seq n (return n)
colon      :: GenParser Char u String
colon      = symbol ":"
\end{code}

\section{Parsing}

We will use Parco to generate an expression parser based on a table of
operators.  The table is sorted by increasing precedence, and while
the format of the table is not directly usable by Parco, we must
maintain information about the names of operators for use in other
parts of the prettyprinter.  For each operator we store its name, its
associativity, and its precedence.

\begin{code}
data OpFun = OpBin Assoc (Term -> Term -> Term)
           | OpPost (Term -> Term)
           | OpPre (Term -> Term)

type OpEntry = (String, Integer, OpFun)
type OpList = [OpEntry]

addOp :: OpEntry -> OpList -> OpList
addOp = insertBy (comparing $ \(_,x,_) -> x)

isOp :: String -> OpList -> Bool
isOp s ops = s `elem` map (\ (x,_,_) -> x) ops
\end{code}

We will store the current list of user-defined operators in the
parsing monad itself, and update the Parco-oriented table whenever
this list is modified.  Some other declarations also cause changes to
the global state, and are likewise stored.

\begin{code}
data DeclState = DeclState {
      userOps   :: OpList
    , abbrevs   :: M.Map String Term
    , expParser :: TwelfParser Term
    }

type TwelfParser = GenParser Char DeclState

defOp :: OpEntry -> TwelfParser ()
defOp e = do
  modifyState $ \s ->
    s { userOps = newOps s
      , expParser = buildExpressionParser (procOpList $ newOps s) termapps }
  genExpParser
    where newOps = addOp e . userOps

genExpParser :: TwelfParser ()
genExpParser = modifyState $ \s -> s { expParser = newFrom s }
    where newFrom s = buildExpressionParser (procOpList $ userOps s) termapps
\end{code}

For example, \textit{abbreviations} are a parse-time mechanism for
expanding identifiers into terms.  Whenever we read an identifier, we
should check whether it has been defined as an abbreviation.

\begin{code}
defAbbrev :: (String, Term) -> TwelfParser ()
defAbbrev (name, t) =
  modifyState $ \s -> s { abbrevs = M.insert name t $ abbrevs s }

maybeExpand :: String -> TwelfParser Term
maybeExpand s = fromMaybe (ident s) <$> M.lookup s <$> abbrevs <$> getState
\end{code}

As a technical aside, we must define the following instance before the
Parco expression parser will work with Parsec.  Note that in the
definition of \texttt{try}, the left-hand side is
\texttt{Text.Parco.try}, while the right-hand side is
\texttt{Text.Parsec.try}.

\begin{code}
instance Text.Parco.Parser TwelfParser where
  try = try
  expects = (<?>)
\end{code}

Initially, only the standard arrow operators are defined.  These could
be wired into the parser itself, but handling them as any other
operator simplifies the rest of the code.

\begin{code}
initOps :: OpList
initOps = [("->", -2, OpBin AssocRight TArrow),
           ("<-", -2, OpBin AssocLeft (flip TArrow)),
           (":",  -1, OpBin AssocLeft TAscription)]

initDeclState :: DeclState
initDeclState =
    DeclState { userOps = []
              , abbrevs = M.empty
              , expParser = fail "expression parser not generated" }

\end{code}

Processing the operator list to a table that Parco can turn into an
expression parser is slightly tricky.  We desire a "maximum munch"
rule (\texttt{<--} should be parsed as the single operator
\texttt{<--}, even if \texttt{<-} is also defined), which is not done
by default.  Fortunately, Parsec provides us with the
\texttt{notFollowedBy} combinator.  We construct the operator parsers
to require that an operator is \textit{not} followed by any character
that could enlargen the token.

\begin{code}
procOpList :: OpList -> OperatorTable TwelfParser Term
procOpList ops = (map (map p) . arrange) $ ops ++ initOps
    where arrange = groupBy (\(_,x,_) (_,y,_) -> x==y) . reverse
          p (name, _, OpBin a f) = Infix (token name *> return f) a
          p (name, _, OpPost f)  = PostfixAssoc (token name *> return f)
          p (name, _, OpPre f)   = PrefixAssoc (token name *> return f)
\end{code}

The actual term parsing is carried out by a triplet of parsers:

\begin{itemize}
\item One for parsing \textit{simple} terms, without any application
  (whether through infix, prefix, or prefix operators) at the top
  level.
\item An \textit{application} parser that parses juxtaposed (applied)
  simple terms, as long as these terms are not operators.
\item A final parser that handles full terms.  It works by applying an
  expression parser that itself applies the previous application
  parser, thus ensuring that application-by-juxtaposition will always
  have higher priority than any defined operator.
\end{itemize}

\begin{code}
term :: TwelfParser Term
term = join (expParser <$> getState) <?> "term"
termapps :: TwelfParser Term
termapps = try notOp `chainl1` pure TApp
    where notOp = do t <- simpleterm
                     ops <- (initOps++) <$> userOps <$> getState
                     when (checkOp t ops) $ fail ""
                     return t
          checkOp (TVar s) = isOp s
          checkOp (TConstant "=") = const True
          checkOp (TConstant s) = isOp s
          checkOp _ = const False
simpleterm :: TwelfParser Term
simpleterm =     parens term
             <|> (token "type" *> return TType)
             <|> (identifier >>= maybeExpand)
             <|> encl TSchem braces
             <|> encl TLambda brackets
             <?> "simple term"
    where encl f brs = pure f
                       <*> brs (uncurry (liftM2 (,))
                                (identifier,
                                 (colon *> term) <|> return THole))
                       <*> term
\end{code}

The |Decl| data type contains all possible Twelf declarations without
loss of information, though the majority are represented through the
``catch-all'' value constructor |DOtherDecl|.

\begin{code}
data Decl = DTerm String Term
          | DDefinition String Term Term
          | DAbbrev String Term
          | DInfix Assoc Integer String
          | DPrefix Integer String
          | DPostfix Integer String
          | DOtherDecl String String
\end{code}

The parser for a single declaration is a trivial rewrite of the |decl|
production rule in Section 3.1 of the Twelf User's Guide.

\begin{code}
decl :: TwelfParser Decl
decl = choice [dabbr, infixd, prfixd, psfixd, odecl, try defd, termd]
       <* symbol "."
    where defd   =     pure DDefinition
                   <*> identifier 
                   <*> ((colon *> term) <|> pure THole) <*> (symbol "=" *> term)
          dabbr  = pure DAbbrev <* token "%abbrev" <*> identifier <*> (symbol "=" *> term)
          infixd = pure DInfix <* token "%infix" <*> opassoc <*> lexeme decimal <*> identifier
          prfixd = pure DPrefix <* token "%prefix" <*> lexeme decimal <*> identifier
          psfixd = pure DPostfix <* token "%postfix" <*> lexeme decimal <*> identifier
          odecl  = pure DOtherDecl <* char '%' 
                   <*> identifier 
                   <*> lexeme (many $ noneOf ".")
          termd  = pure DTerm <*> identifier <*> (colon *> term)

opassoc :: GenParser Char u Assoc
opassoc = token "none"  *> pure AssocNone <|>
          token "left"  *> pure AssocLeft <|>
          token "right" *> pure AssocRight
\end{code}

The full signature parser is the only one that skips leading
whitespace.  Apart from that, it continuously reads declarations until
reaching end of file.  Some declarations may affect the parsing of
later ones, and are treated specially, but all end up in the final
parse result.

\begin{code}
sig :: TwelfParser [Decl]
sig = whiteSpace *> sig'
    where sig' = (eof *> pure []) <|> do
            d <- decl
            case d of
              DAbbrev s t  -> defAbbrev (s, t)
              DInfix a p s -> defOp (s, p, OpBin a $ TApp . TApp (ident s))
              DPrefix p s  -> defOp (s, p+10000, OpPre $ TApp (ident s))
              DPostfix p s -> defOp (s, p+10000, OpPost $ TApp (ident s))
              _            -> return ()
            (d:) <$> sig'
\end{code}

Finally, we define shallow interface functions for running the parser.

\begin{code}
parseDecl :: DeclState
          -> SourceName
          -> String
          -> Either ParseError (Decl, DeclState)
parseDecl = runP (pure (,) <*> (genExpParser *> decl) <*> getState)

parseSig :: DeclState
         -> SourceName 
         -> String 
         -> Either ParseError ([Decl], DeclState)
parseSig = runP (pure (,) <*> (genExpParser *> sig) <*> getState)
\end{code}

\section{Configuration file}

The syntax for Twelf configuration files is sadly completely
unspecified.  The parser implemented here reads a file name per line,
and permits the same syntax for block- and line-comments as the rest
of Twelf, with the caveat that all comments have to start at the
beginning of a line (that is, you can have file names that contain
percentage signs).

\begin{code}
config :: GenParser Char () [String]
config = whiteSpace *> many (lexeme $ many1 $ noneOf "\n")

parseConfig :: SourceName
            -> String
            -> Either ParseError [String]
parseConfig = parse config
\end{code}

\section{Unparsing}

We define |Show| instances for turning |Term|s and |Declaration|s into
strings that, if parsed again, would result in values identical to the
originals.  That is, the parsers and these |Show| instances are
inverse operations of each other.

\begin{code}
instance Show Term where
    show TType = "type"
    show (TArrow t1 t2) = 
      "(" ++ show t1 ++ ") -> " ++ show t2
    show (TSchem (s, t1) t2) = 
      "{" ++ s ++ ":" ++ show t1 ++ "} " ++ show t2
    show (TLambda (s, t1) t2) =
      "[" ++ s ++ ":" ++ show t1 ++ "] " ++ show t2
    show (TApp t1 t2) =
      "(" ++ show t1 ++ " " ++ show t2 ++ ")"
    show (TAscription t1 t2) =
      "(" ++ show t1 ++ " : " ++ show t2 ++ ")"
    show THole = "_"
    show (TVar s) = s
    show (TConstant s) = s
\end{code}

\begin{code}
instance Show Decl where
    show d = up d ++ "."
        where up (DTerm s t) = s ++ " : " ++ show t
              up (DDefinition s t e) = s ++ " : " ++ show t ++ " = " ++ show e
              up (DAbbrev s t) = "%abbrev " ++ s ++ " = " ++ show t
              up (DInfix a p s) = "%infix " ++ showAssoc a ++ " " ++ show p ++ " " ++ s
              up (DPrefix p s) = "%prefix " ++ show p ++ " " ++ s
              up (DPostfix p s) = "%prefix " ++ show p ++ " " ++ s
              up (DOtherDecl p s) = "%" ++ p ++ " " ++ s
              showAssoc AssocLeft = "left"
              showAssoc AssocRight = "right"
              showAssoc AssocNone = "none"
\end{code}

\section{Interpreting as LF}

Obtaining a parse tree of a Twelf program is all well and good, but it
is quite cumbersome to work with.  In \Fref{chap:lf representation} we
defined data types much closer to the usual interpretation of LF, and
we therefore need to be able to convert our |Decl|s and |Term|s to an
|LF.Signature| containing |LF.Type|s and |LF.Object|s.  We only work
on fully reconstructed terms (though see
\Fref{chap:twelfppr.reconstruct}).

Recall that an |LF.Signature| is merely a mapping from names of type
families to type families.  Our algorithm therefore scans through the
declaration list, looking for type family definitions.  If one is
found, it will scan through the rest of the list looking for type
definitions in that family.  We define the \textit{conclusion} of a
term as the body of any $\Pi$-constructs.

\begin{code}
conclusion :: Term -> Term
conclusion (TArrow _ t) = conclusion t
conclusion (TSchem _ t) = conclusion t
conclusion t            = t

isFamDef :: Term -> Bool
isFamDef t = conclusion t == TType

toSignature :: [Decl] -> LF.Signature
toSignature ds = M.fromList $ mapMaybe convert ds
    where convert (DTerm s t)
              | isFamDef t =
                  Just ( LF.TyFamRef s
                       , buildFamily kr k ds)
              where kr = LF.TyFamRef s
                    k  = toKind M.empty t
          convert _ = Nothing
\end{code}

\begin{code}
toKind :: M.Map String LF.Type -> Term -> LF.Kind
toKind _ TType = LF.KiType
toKind vs (TArrow t1 t2) =
  LF.KiCon Nothing (toType vs t1) (toKind vs t2)
toKind vs (TSchem (name, t1) t2) =
  LF.KiCon (Just tr) ty1 k
      where vs' = M.insert name ty1 vs
            ty1 = toType vs t1
            k   = toKind vs' t2
            tr  = LF.VarRef name
toKind _ _ = error "Invalid kind declaration"
\end{code}

We need to gather all the definitions that constitute a member of the
type family that we are interested in.  A term definition is eligible
if its conclusion (see above) is in the type family.

\begin{code}
buildFamily :: LF.TyFamRef -> LF.Kind -> [Decl] -> LF.TyFamDef
buildFamily (LF.TyFamRef s) k ds =
  LF.TyFamDef k (consts ds) (abbs ds)
    where pickCs (DTerm tr t) 
              | ok (conclusion t) = Just (LF.ConstRef tr, t)
          pickCs _ = Nothing
          pickAs (DDefinition tr t1 t2)
              | ok (conclusion t1) = Just (LF.ConstRef tr, t1, t2)
          pickAs _ = Nothing
          ok (TApp t _)        = ok t
          ok (TConstant s2)    = s == s2
          ok (TAscription t _) = ok t
          ok _                 = False
          convertT (name, t)   = (name, toType M.empty t)
          convertA (name, ty, t)   = ( name
                                     , toType M.empty ty
                                     , toObject M.empty t)
          consts  = map convertT . mapMaybe pickCs
          abbs    = map convertA . mapMaybe pickAs
\end{code}

Objects and types are merged in a single syntactical category in
Twelf, but they are distinct concepts in LF type theory.  Hence, we
define two different conversion functions, based on whether we expect
a type or an object in some position.  This means that, for instance,
a |TApp| is interpreted differently based on whether it is in a type
or object context.  Additionally, we keep track of variables bound by
$\lambda$- and $\Pi$-abstraction, so we can determine whether a given
name is a constant or a variable, rather than relying solely on case.
This is necessary as there is no requirement on the case of variables
in explicit bindings, and as we deal with fully reconstructed terms,
there should be no implicit variables at all.

Arrows and $\Pi$-constructs are trivially converted to the
corresponding LF type.  Note that an arrow in Twelf is just a
syntactic shortcut for a $\Pi$ constructor in which the variable is
not free in the enclosed term.

\begin{code}
toType :: M.Map String LF.Type -> Term -> LF.Type
toType vs (TArrow t1 t2) =
  LF.TyCon Nothing (toType vs t1) (toType vs t2)
toType vs (TSchem (name, t1) t2) = 
  LF.TyCon (Just $ LF.VarRef name) ty1 ty2
      where ty1 = toType vs t1
            vs' = M.insert name ty1 vs
            ty2 = toType vs' t2
\end{code}

Application is quite simple too, the |TApp|s in the Twelf syntax
correspond exactly to the |TyApp|s at the LF level.  We treat a
constant or variable by itself as the kind named by the constant
applied to zero arguments.

\begin{code}
toType vs (TApp t1 t2) =
  LF.TyApp (toType vs t1) (toObject vs t2)
toType _ (TConstant name) = LF.TyName (LF.TyFamRef name)
toType _ (TVar name)      = LF.TyName (LF.TyFamRef name)
\end{code}

Type ascriptions are completely ignored: they have no semantic value.

\begin{code}
toType vs (TAscription t _) = toType vs t
\end{code}

The constant \texttt{type} is not permitted in types, only in type
family definitions.  The presence of holes is also not permitted, and
type reconstruction should be performed to remove them.  Finally,
lambda bindings is only permitted in objects.

\begin{code}
toType _ TType = error "'type' found where actual type expected in term"
toType _ THole    = error "Cannot convert incomplete term to object"
toType _ (TLambda _ _) = 
    error "Object found where type or kind expected in term"
\end{code}

Converting terms to objects is trivial.  Again, we ignore any type
ascriptions.

\begin{code}
toObject :: M.Map String LF.Type -> Term -> LF.Object
toObject vs (TLambda (name, t1) t2) = 
  LF.Lambda (LF.VarRef name) ty1 (toObject vs' t2)
      where vs' = M.insert name ty1 vs
            ty1 = toType vs t1
toObject vs (TVar t) =
  maybe constant var $ M.lookup t vs
    where constant = LF.Const $ LF.ConstRef t
          var      = LF.Var (LF.VarRef t)
toObject vs (TConstant t) =
  maybe constant var $ M.lookup t vs
    where constant = LF.Const $ LF.ConstRef t
          var      = LF.Var (LF.VarRef t)
toObject vs (TApp t1 t2)      =
  LF.App (toObject vs t1) (toObject vs t2)
toObject vs (TAscription t _) = toObject vs t
toObject _ THole              =
  error "Cannot convert incomplete term to object"
toObject _ _                  =
  error "Type found where object expected in term"
\end{code}
