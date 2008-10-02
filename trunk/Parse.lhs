
> module Parse ( lexer
>              , ReadT(..)
>              , Parser
>              , leftInfix
>              , rightInfix
>              , list
>              , bracketed
>              , formulaBracket
>              , termBracket
>              , makeParser
>              , pair
>              , many
>              , until )
>   where

> import Prelude hiding (until)
> import qualified List
> import qualified Char

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Lexical Analysis                                                          

> lexer :: String -> [String]
> lexer [] = []
> lexer ('%':cs) = case List.elemIndex '\n' cs of
>                    Nothing -> []
>                    Just n -> lexer (drop n cs)
> lexer s@(c:cs) | elem c [' ','\t','\n'] = lexer cs 
>                | elem c punctuation = [c]:lexer cs
>                | Char.isAlpha c = lexVar s 
>                | Char.isDigit c = lexInt s 
>                | isSymbol c = lexSym s
>                | True = error ("lexical error: " ++ [c])

> lexVar :: String -> [String]
> lexVar (c:cs) = (c:var) : lexer rest
>   where (var, rest) = span (\x -> Char.isAlphaNum x || elem x "_'") cs
> lexVar _ = error "Impossible" 

> lexInt :: String -> [String]
> lexInt s = n : lexer rest
>   where (n, rest) = span Char.isDigit s

> lexSym :: String -> [String]
> lexSym s = sym : lexer rest 
>   where (sym, rest) = span isSymbol s 

> symbols :: String
> symbols = "<>=|&~+-*/\\^:,."

> punctuation :: String
> punctuation = "()[]{}"

> isSymbol :: Char -> Bool
> isSymbol x = elem x symbols

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Parsing

> type Parser a = [String] -> Maybe (a, [String])

Token reader

> class ReadT a where
>   readt :: Parser a
>   parse :: String -> a
>   parse = makeParser readt

> makeParser :: Parser a -> String -> a
> makeParser p s = case p (lexer s) of
>                  Nothing -> error "Parse error"
>                  Just (e, []) -> e
>                  Just (_, toks) -> error ("unconsumed tokens: " ++ show toks)

Combinators

> literal :: String -> Parser String 
> literal x (x':rest) = if x == x' then Just(x, rest) else Nothing 
> literal _ [] = Nothing

> (+++) :: Parser a -> Parser b -> Parser (a, b)
> (p1 +++ p2) inp = case p1 inp of
>                 Nothing -> Nothing 
>                 Just (x, rest) -> case p2 rest of
>                                   Nothing -> Nothing
>                                   Just (y, rest') -> Just ((x, y), rest')

> with :: Parser a -> (a -> b) -> Parser b
> (p `with` f) inp = case p inp of
>                    Nothing -> Nothing
>                    Just (x, rest) -> Just(f x, rest)

> (>>>) :: Parser a -> Parser b -> Parser b
> p1 >>> p2 = (p1 +++ p2) `with` (\(_, b) -> b)

> (<<<) :: Parser a -> Parser b -> Parser a
> p1 <<< p2 = (p1 +++ p2) `with` (\(a, _) -> a)

> pair :: Parser a -> Parser b -> Parser (a, b)
> pair p1 p2 = literal "(" >>> p1 <<< literal "," +++ p2 <<< literal ")"

> many :: Parser a -> Parser [a]
> many p inp = case p inp of 
>                Nothing -> Just ([], inp)
>                Just (x, rest) -> case many p rest of
>                                    Nothing -> error "Impossible"
>                                    Just (xs, rest') -> Just (x:xs, rest')

> until :: (String -> Bool) -> Parser String
> until f = until' [] 
>   where until' acc [] = Just (List.concat (reverse acc), [])
>         until' acc (inp@(h:t)) = if f h then Just(List.concat (reverse acc), inp)
>                                  else until' (h:acc) t

We often need to parse infix operators of various kinds, e.g. the logical
connectives like ==> and the arithmetic operators like +. For most of these
we adopt a policy of right-association, i.e. interpreting a * b * c as a * (b * c).
However this is a bit unnatural for '-', since we want to read x - y - z as
(x − y) − z not x − (y − z). We therefore want to be able to insist on either
left or right associativity. Both can be subsumed by the following generic
parsing function that lets us associate the subitems however we want:

> ginfix :: String -> ((a -> b) -> a -> a -> b) 
>             -> (a -> b) -> Parser a -> Parser b
> ginfix opsym opupdate sof subparser inp = 
>   case subparser inp of
>     Nothing -> Nothing
>     Just (e1, inp1) -> 
>       case inp1 of 
>         opsym':inp2 -> 
>           if opsym == opsym' then
>              ginfix opsym opupdate (opupdate sof e1) subparser inp2
>           else Just (sof e1, inp1)
>         _ -> Just (sof e1, inp1)

This takes two function arguments: sof takes the current input and combines
it in some way with the items arrived at so far, while opupdate modifies
the function appropriately when a new item is parsed. This may look obscure,
but it should become clearer looking at the following examples, which
show how using the same core function we can parse a list of items and either
combine them in a left or right associated manner, or even just collect them
all into a list. We will use the last of these to parse the list of arguments to
a function f(t1, t2, . . . , t3), treating the comma as another infix symbol.

> leftInfix :: String -> (a -> a -> a) -> Parser a -> Parser a
> leftInfix opsym opcon = ginfix opsym (\f e1 e2 -> opcon (f e1) e2) id

> rightInfix :: String -> (a -> a -> a) -> Parser a -> Parser a
> rightInfix opsym opcon = ginfix opsym (\f e1 e2 -> f (opcon e1 e2)) id

> list :: String -> Parser a -> Parser [a]
> list opsym = ginfix opsym (\f e1 e2 -> f e1 ++ [e2]) (\x -> [x])

This function deals with the common situation of syntactic items
enclosed in brackets. It simply calls the subparser and then checks and
eliminates the closing bracket. In principle, the terminating character can
be anything, so this function could equally be used for other purposes, but
we will always use ‘)’ for the cbra (‘closing bracket’) argument.

> bracketed :: Parser a -> String -> Parser a
> bracketed subparser cbra inp = 
>   case subparser inp of
>     Nothing -> Nothing
>     Just (ast, cbra':rest) -> 
>       if cbra == cbra' then Just (ast, rest)
>       else Nothing
>     _ -> Nothing

We use Harrison's quoting style for formulas, e.g.
 <<forall x. exists y. p(x,y) \/ q>>

> formulaBracket :: Parser a -> Parser a
> formulaBracket _ [] = Nothing
> formulaBracket p (h:t) = 
>   if take 2 h == "<<" then 
>      if drop 2 h == "" then (p <<< literal ">>") t
>      else (p <<< literal ">>") (drop 2 h : t)
>   else Nothing
> termBracket :: Parser a -> Parser a
> termBracket p = literal "<<|" >>> p <<< literal "|>>"
