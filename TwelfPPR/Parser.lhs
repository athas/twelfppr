%----------------------------------------------------------------------------
%--
%-- Module      :  TwelfPPR.Parser
%-- Copyright   :  (c) Troels Henriksen 2009
%-- License     :  BSD3-style (see LICENSE)
%--
%-----------------------------------------------------------------------------

\begin{ignore}
\begin{code}
{-# LANGUAGE PackageImports #-}
\end{code}
\end{ignore}

\chapter{|TwelfPPR.Parser|}

This chapter implements a parser for the Twelf implementation of the
ELF programming language.  The entire language is supported, including
all syntactical shortcuts and conveniences provided by Twelf.

The parser is constructed through the Parsec library of parser
combinators.  This may cost performance, compared to using a
traditional parser generator, but not to a degree significant for our
uses, especially considering the relatively small size of normal Twelf
programs.

\begin{code}
module TwelfPPR.Parser ( Term(..)
                       , Decl(..)
                       , DeclState(..)
                       , initDeclState
                       , parseDecl
                       , parseSig
                       , parseConfig
) where

import Control.Applicative
import Control.Monad
import "mtl" Control.Monad.Identity
import "mtl" Control.Monad.Trans

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Ord

import Debug.Trace

import Text.Parsec hiding ((<|>), many, optional)
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T

--import TwelfPPR.LF
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
idChar = satisfy $ \c -> and [ not $ c `elem` idReserved
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

lowcaseId :: String -> Bool
lowcaseId = not . upcaseId

ident :: String -> Term
ident "_"            = THole
ident s | upcaseId s = TVar s
        | otherwise  = TConstant s
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
semi-common in actual Twelf code.

It is therefore necessary that we define our own lexer.  Fortunately,
this is not very hard in Parsec.  The following definitions all
discard trailing whitespace and comments, thereby assuming that there
is no leading whitespace.

\begin{code}
whiteSpace :: GenParser Char u ()
whiteSpace = skipMany (simpleSpace <|> oneLineComment <|> multiLineComment <?> "")
    where oneLineComment = do try (    try (string "% ")
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
          simpleSpace = skipMany1 (satisfy isSpace)

lexeme     :: GenParser Char u a -> GenParser Char u a
lexeme p   = p <* whiteSpace
symbol     :: String -> GenParser Char u String
symbol     = lexeme . string
identifier :: GenParser Char u String
identifier = lexeme $ (many1 idChar <?> "identifier")
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

We store operators in a table (sorted by increasing precedence).  This
is not directly usable by Parsec, but we desire to maintain
information about the names of operators for use in other parts of the
prettyprinter.  For each operator we store its name, its
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
parsing monad itself, and update the Parsec-oriented table whenever
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
maybeExpand s = maybe (ident s) id <$> M.lookup s <$> abbrevs <$> getState
\end{code}

Initially, only the standard arrow operators are defined.  These could
be wired into the parser itself, but handling them as any other
operator simplifies the rest of the code.

\begin{code}
initOps :: OpList
initOps = [("->", -1, OpBin AssocRight TArrow), 
           ("<-", -1, OpBin AssocLeft (flip TArrow))]

initDeclState :: DeclState
initDeclState = 
    DeclState { userOps = []
              , abbrevs = M.empty
              , expParser = fail "expression parser not generated" }

\end{code}

Processing the operator list to a table, that Parsec can turn into an
expression parser, is slightly tricky.  We desire a "maximum munch"
rule (\texttt{<--} should be parsed as the single operator
\texttt{<--}, even if \texttt{<-} is also defined), which is not done
by default.  Fortunately, Parsec provides us with the
\texttt{notFollowedBy} combinator.  We construct the operator parsers
to require that an operator is \textit{not} followed by any character
that could enlargen the token.

\begin{code}
procOpList :: OpList -> OperatorTable [Char] DeclState Identity Term
procOpList ops = (map (map f) . arrange) $ ops ++ initOps
    where arrange = groupBy (\(_,x,_) (_,y,_) -> x==y) . reverse
          f (name, _, OpBin a f) = Infix (try $ token name *> return f) a
          f (name, _, OpPost f)  = Postfix (try $ token name *> return f)
          f (name, _, OpPre f)   = Prefix (try $ token name *> return f)
          token s = lexeme (string s *> notFollowedBy idChar)
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
term = do xp <- expParser <$> getState
          xp `chainl1` (colon *> pure TAscription <|> pure TApp)
termapps :: TwelfParser Term
termapps = try notOp `chainl1` (colon *> pure TAscription <|> pure TApp)
    where notOp = do t <- simpleterm
                     ops <- (initOps++) <$> userOps <$> getState
                     when (checkOp t ops) $ fail ""
                     return t
          checkOp (TVar s) = isOp s
          checkOp (TConstant "=") = const True
          checkOp (TConstant s) = isOp s
          checkOp _ = const False
simpleterm :: TwelfParser Term
simpleterm =     try (parens term)
             <|> try (symbol "type" *> return TType)
             <|> try (maybeExpand =<< identifier)
             <|> try (encl TSchem braces)
             <|> try (encl TLambda brackets)
    where encl f brs = (pure f
                        <*> brs (uncurry (liftM2 (,))
                                 (identifier, 
                                  (colon *> term) <|> return THole))
                        <*> term)
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
          | DName String String (Maybe String)
          | DOtherDecl String String
\end{code}

\begin{code}
decl :: TwelfParser Decl
decl = (choice $ map try
        [dabbr, infixd, prfixd, psfixd, odecl, defd, termd]) 
       <* symbol "."
    where defd   = pure DDefinition <*> identifier <*> ((colon *> term) <|> pure THole) <*> (symbol "=" *> term)
          dabbr  = pure DAbbrev <* symbol "%abbrev" <*> identifier <*> (symbol "=" *> term)
          infixd = pure DInfix <* symbol "%infix" <*> opassoc <*> lexeme decimal <*> identifier
          prfixd = pure DPrefix <* symbol "%prefix" <*> lexeme decimal <*> identifier
          psfixd = pure DPostfix <* symbol "%postfix" <*> lexeme decimal <*> identifier
          odecl  = pure DOtherDecl <* char '%' 
                   <*> identifier 
                   <*> lexeme (many $ noneOf ".")
          termd  = pure DTerm <*> identifier <*> (colon *> term)

opassoc :: GenParser Char u Assoc
opassoc = symbol "none"  *> pure AssocNone <|>
          symbol "left"  *> pure AssocLeft <|>
          symbol "right" *> pure AssocRight
\end{code}

\begin{code}
sig :: TwelfParser [Decl]
sig = whiteSpace *> sig'
    where sig' = (eof *> pure []) <|> do
                   d <- decl
                   case d of
                     DAbbrev s t -> do
                       defAbbrev (s, t)
                       (d:) <$> sig'
                     DInfix a p s -> do
                       defOp $ (s, p, OpBin a $ TApp . TApp (ident s))
                       (d:) <$> sig'
                     DPrefix p s -> do
                       defOp $ (s, p, OpPre $ TApp (ident s))
                       (d:) <$> sig'
                     DPostfix p s -> do
                       defOp $ (s, p, OpPost $ TApp (ident s))
                       (d:) <$> sig'
                     _            -> (d:) <$> sig'
\end{code}

Finally, we define shallow interface functions for running the parser.

\begin{code}
parseDecl :: DeclState
          -> SourceName
          -> String
          -> Either ParseError (Decl, DeclState)
parseDecl s = runP (uncurry (liftA2 (,)) (genExpParser *> decl,
                                          getState)) s

parseSig :: DeclState
         -> SourceName 
         -> String 
         -> Either ParseError ([Decl], DeclState)
parseSig s = runP (uncurry (liftA2 (,)) (genExpParser *> sig, getState)) s
\end{code}

\section{Sources file}

\begin{code}
config :: GenParser Char () [String]
config = many $ many1 (noneOf "\n") <* many newline
\end{code}

\begin{code}
parseConfig :: SourceName
             -> String
             -> Either ParseError [String]
parseConfig = parse config
\end{code}

\section{Unparsing}

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
      show t1 ++ " : " ++ show t2
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

\section{Testing}

\begin{code}
testp :: Either ParseError [Decl]
testp = runP (genExpParser *> sig) initDeclState "" $ intercalate "\n" input
    where input = ["%",
                   "t : a -> b -> type.",
                   "d : a <- b <- {x} c x -> p x.",
                   "d : ({x} c x -> p x) -> b -> a.",
                   "d : ((a <- b) <- ({x:_} ((c x) -> (p x)))).",
                   "d : ((a <~ b) <~ ({x:_} ((c x) ~> (p x)))).",
                   "%abbrev Int# = ptp PInt#.",
                   "w : Int#.",
                   "%unknown definition.",
                   "%infix left 0 <~.",
                   "% fooobar",
                   "%infix right 0 ~>.",
                   "t : (a ~> a) ~> a ~> type.",
                   "d : ((a <~ b) <~ ({x:_} ((c x) ~> (p x)))).",
                   "%%bazraaa",
                   "t : a -> b -> type.",
                   "myexp : exp = lam[x] case x (s z) [y] z."]

ttestp :: Either ParseError Term
ttestp = runP (genExpParser *> term) initDeclState "" $ intercalate "\n" input
    where input = ["a b"]

test :: IO ()
test = either print (mapM_ print) testp
ttest :: IO ()
ttest = print ttestp
\end{code}
