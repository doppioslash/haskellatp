
A simple expression language. 

E ::= P + E | P
P ::= A + P | A
A ::= ( E ) | Int | Var

Int = [0-9]+
Var = [a-zA-Z][a-zA-Z0-9]*

Note that by this grammar, '+' and '*' are right associative.

> module Intro ( Expr(Var, Const, Add, Mul)
>              , simplify
>              , parse
>              ) where

> import Prelude
> import qualified Char 
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJ( (<+>) )
> import Parse(ReadT,Parser)
> import qualified Parse
> import Print(PP)
> import qualified Print

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Expressions

> data Expr = Var String
>           | Const Int
>           | Add Expr Expr
>           | Mul Expr Expr

For example

Add (Mul (Const 2) (Var "x")) (Var "y")

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Simplification

> simplify :: Expr -> Expr
> simplify (Add e1 e2) = simplify1 (Add (simplify e1) (simplify e2))
> simplify (Mul e1 e2) = simplify1 (Mul (simplify e1) (simplify e2))
> simplify e = e

> simplify1 :: Expr -> Expr
> simplify1 (Add (Const m) (Const n)) = Const $ m + n
> simplify1 (Mul (Const m) (Const n)) = Const $ m * n
> simplify1 (Add (Const 0) x) = x
> simplify1 (Add x (Const 0)) = x
> simplify1 (Mul (Const 0) _) = Const 0
> simplify1 (Mul _ (Const 0)) = Const 0
> simplify1 (Mul (Const 1) x) = x
> simplify1 (Mul x (Const 1)) = x
> simplify1 x = x

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Parsing

> instance ReadT Expr where
>   readt = parseExpr

> parse :: String -> Expr
> parse = Parse.parse

E ::= P + E | P 

> parseExpr :: Parser Expr
> parseExpr toks = 
>   case parseProd toks of
>     Just (e1, "+" : toks1) -> 
>       case parseExpr toks1 of
>         Just (e2, toks2) -> Just (Add e1 e2, toks2) 
>         x -> x
>     x -> x

P ::= A + P | A

> parseProd :: Parser Expr
> parseProd toks = 
>   case parseAtom toks of
>     Just (e1, "*" : toks1) -> 
>       case parseProd toks1 of 
>         Just (e2, toks2) -> Just (Mul e1 e2, toks2)
>         x -> x
>     x -> x

A ::= ( E ) | Int | Var 

> parseAtom :: Parser Expr
> parseAtom ("(" : toks) = 
>   case parseExpr toks of
>     Just (e, ")" : toks1) -> Just(e, toks1)
>     _ -> error "Impossible" 
> parseAtom (tok@(c:_) : toks) = 
>   if Char.isDigit c then Just (Const (read tok), toks)
>   else Just (Var tok, toks)
> parseAtom _ = Nothing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Printing

Print "+" and "*" as right associative by including
a precedence argument.

We use the Hughes pretty printing library for layout.

> instance Show Expr where
>      show e = (PP.renderStyle Print.ppStyle (pp' 0 e))

> instance PP Expr where
>   pp = pp' 0

> pp' :: Int -> Expr -> PP.Doc
> pp' _ (Var s) = PP.text s
> pp' _ (Const n) = PP.int n
> pp' pr (Add e1 e2) = 
>      let doc1 = pp' 3 e1 
>          doc2 = pp' 2 e2 
>          doc3 = doc1 <+> PP.text "+" <+> doc2 in
>      if pr > 2 then PP.parens doc3 else doc3
> pp' pr (Mul e1 e2) = 
>      let doc1 = pp' 5 e1 
>          doc2 = pp' 4 e2 
>          doc3 = doc1 <+> PP.text "*" <+> doc2 in
>      if pr > 4 then PP.parens doc3 else doc3
