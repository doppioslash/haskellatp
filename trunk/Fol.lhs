
First order logic.  Atomic formulas are now relations on
terms where terms are either functions applied to arguments
or variables.

Terms T ::= T '::' T1 | T1
      T1 ::= T1 + T2 | T2
      T2 ::= T3 - T2 | T3
      T3 ::= T3 * T4 | T4
      T4 ::= T5 / T4 | T5
      T5 ::= T6 ^ T5 | A

Term lists TS ::= T | T , TS

Atoms A ::= ( T ) | - A | Var () | Var ( TS ) | Var

Relations R ::= Var() | Var ( TS ) | Var | T = T | T < T 
              | T <= T | T > T | T >= T

> module Fol ( Fol(R)
>            , onformula
>            , Term(Var, Fn)
>            , isVar
>            , Env
>            , Fv(fv)
>            , Subst(apply)
>            , generalize
>            , functions
>            , predicates
>            , variant
>            , holds
>            , parse
>            , parser
>            , parseTerm
>            ) where

> import Prelude 
> import qualified List 
> import qualified Char 
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJ( (<>) ) 

> import Lib((|->))
> import qualified Lib
> import Print(PP)
> import qualified Print
> import Parse(ReadT, Parser)
> import qualified Parse
> import qualified ListSet
> import ListSet((\\))
> import Formulas(Formula(..), (\/), (/\), (==>), (<=>), Var, Vars, Sym )
> import qualified Formulas as F

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Terms

> data Term = Var Var
>           | Fn Sym [Term]
>             deriving (Eq, Ord)

> isVar :: Term -> Bool
> isVar (Var _) = True
> isVar _ = False

> instance Num Term where
>   t1 + t2 = Fn "+" [t1, t2]
>   t1 - t2 = Fn "-" [t1, t2]
>   t1 * t2 = Fn "*" [t1, t2]
>   negate t = Fn "-" [t]
>   abs _ = error "Unimplemented" 
>   signum _ = error "Unimplemented" 
>   fromInteger n = Fn (show n) []

%%%%%%%%%%%%%%
%%% Parsing

> instance ReadT Term where
>   readt = parseTerm' [] 

> parse :: String -> Formula Fol
> parse = Parse.makeParser parser

> parser :: Parser (Formula Fol)
> parser = Parse.formulaBracket Parse.readt

> parseTerm :: String -> Term
> parseTerm = Parse.makeParser (Parse.termBracket Parse.readt)

> parseTerm' :: Vars -> Parser Term
> parseTerm' vs = 
>   Parse.rightInfix "::" (fn "::")
>     (Parse.rightInfix "+" (fn "+")
>        (Parse.leftInfix "-" (fn "-")
>          (Parse.rightInfix "*" (fn "*")
>            (Parse.leftInfix "/" (fn "/")
>              (Parse.leftInfix "^" (fn "^")
>                 (parseAtomic vs))))))
>   where fn op e1 e2 = Fn op [e1, e2]

> parseAtomic :: Vars -> Parser Term
> parseAtomic vs cs = case cs of 
>   [] -> Nothing
>   "(":rest -> Parse.bracketed (parseTerm' vs) ")" rest
>   "-":rest -> case parseAtomic vs rest of
>                 Nothing -> Nothing
>                 Just (t, rest1) -> Just (Fn "-" [t], rest1)
>   f:"(":")": rest -> Just(Fn f [], rest)
>   f:"(":rest -> case Parse.bracketed (Parse.list "," (parseTerm' vs)) ")" rest of
>                   Nothing -> Nothing
>                   Just (args, rest1) -> Just(Fn f args, rest1)
>   a:rest -> Just (if const a && not(elem a vs) then Fn a [] else Var a, rest)
>   where const tok@(c:_) = Char.isDigit c || tok == "nil"
>         const _ = error "Impossible" 

%%%%%%%%%%%%%%%
%%% Printing

> instance Show Term where
>     show tm = PP.renderStyle Print.ppStyle (PP.text "<<|" <> Print.pp tm <> PP.text"|>>")

> instance PP Term where
>   pp = ppTerm' 0

> ppTerm' :: Int -> Term -> PP.Doc
> ppTerm' prec tm = case tm of  
>    Var x -> PP.text x
>    Fn "^" [tm1, tm2] -> ppInfixTm True prec 24 "^" tm1 tm2
>    Fn "/" [tm1, tm2] -> ppInfixTm True prec 22 "/" tm1 tm2
>    Fn "*" [tm1, tm2] -> ppInfixTm True prec 20 "*" tm1 tm2
>    Fn "-" [tm1, tm2] -> ppInfixTm True prec 18 "-" tm1 tm2
>    Fn "+" [tm1, tm2] -> ppInfixTm True prec 16 "+" tm1 tm2
>    Fn "::" [tm1, tm2] -> ppInfixTm True prec 14 "::" tm1 tm2
>    Fn f [] -> PP.text f
>    Fn f xs -> PP.text f <> ppArgs xs

> ppArgs :: [Term] -> PP.Doc
> ppArgs xs =
>   PP.parens (PP.sep (PP.punctuate (PP.text ",") (map (ppTerm' 0) xs)))

> ppInfixTm :: Bool -> Int -> Int -> String -> Term -> Term -> PP.Doc
> ppInfixTm isleft oldprec newprec sym p q = 
>   let pprec = if isleft then newprec else newprec + 1
>       qprec = if isleft then newprec + 1 else newprec
>       doc1 = ppTerm' pprec p
>       doc2 = ppTerm' qprec q 
>       doc = PP.sep[doc1, PP.text sym, doc2] in
>   if oldprec > newprec then PP.parens doc else doc

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Relations

> data Fol = R Sym [Term]
>            deriving (Eq, Ord)

  
> onformula :: (Term -> Term) -> Formula Fol -> Formula Fol
> onformula f = F.onatoms(\(R p a) -> Atom(R p (map f a)))


%%%%%%%%%%%%%%
%%% Parsing

> instance ReadT Fol where
>   readt = parseAtom [] 

> parseAtom :: Vars -> Parser Fol
> parseAtom vs inp =
>   case parseBinop vs inp of
>     j@(Just _) -> j
>     Nothing -> case inp of 
>       p:"(":")":rest -> Just (R p [], rest)
>       p:"(":rest -> 
>         case Parse.bracketed (Parse.list "," (parseTerm' vs)) ")" rest of
>           Nothing -> Nothing
>           Just (args, rest1) -> Just(R p args, rest1)
>       p:rest | p /= "(" -> Just (R p [], rest)
>       _ -> Nothing

> parseBinop :: Vars -> Parser Fol
> parseBinop vs inp = 
>   do (tm1, r:rest) <- parseTerm' vs inp 
>      (tm2, rest') <- if not (elem r ["=", "<", "<=", ">", ">="]) then fail "expecting binop" else parseTerm' vs rest
>      return (R r [tm1, tm2], rest')

%%%%%%%%%%%%%%%
%%% Printing

> instance Show Fol where
>     show rel = PP.renderStyle Print.ppStyle (Print.pp rel)

> instance PP Fol where
>   pp (R p []) = PP.text p
>   pp (R p args) = 
>     if List.elem p ["=", "<", "<=", ">", ">="] && length args == 2 
>     then ppInfixTm False 12 12 p (args !! 0) (args !! 1)
>     else PP.text p <> ppArgs args

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Free Variables

> class Fv a where
>   fv :: a -> Vars

> instance Fv Term where
>   fv (Var x) = [x]
>   fv (Fn _ args) = ListSet.unions (map fv args)

> instance Fv Fol where
>   fv (R _ args) = ListSet.unions (map fv args)

> instance Fv a => Fv (Formula a) where
>   fv fm = case fm of
>           Top -> []
>           Bot -> []
>           Not p -> fv p
>           Forall x p -> fv p \\ [x]
>           Exists x p -> fv p \\ [x]
>           And p q -> combine p q
>           Or p q -> combine p q
>           Imp p q -> combine p q
>           Iff p q -> combine p q
>           Atom a -> fv a
>     where combine p q = ListSet.union (fv p) (fv q)

> instance Fv a => Fv [a] where
>   fv xs = ListSet.unions (map fv xs)

> generalize :: Formula Fol -> Formula Fol
> generalize fm = foldr Forall fm (fv fm) 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Function symbols with arity

> functions :: Formula Fol -> [(Sym, Int)]
> functions = F.atomUnion (\(R _ args) -> foldr (ListSet.union . funcs) [] args) 

> funcs :: Term -> [(Sym, Int)]
> funcs (Var _) = []
> funcs (Fn f args) = foldr (ListSet.union . funcs) [(f, length args)] args 

> predicates :: Formula Fol -> [(Sym, Int)]
> predicates = F.atomUnion (\(R p args) -> [(p, length args)])

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Environments

This is generally the correct type for substitutions.  There is one exception
in EqElim where Map Term Term is needed

> type Env = Map Var Term

%%%%%%%%%%%%%%%%%%%%
%%% Substitutions

> class Subst a where
>   apply :: Env -> a -> a

> instance Subst Term where
>   apply env tm = case tm of
>                  Var x -> case Map.lookup x env of
>                           Just t -> t
>                           Nothing -> tm
>                  Fn f args -> Fn f (map (apply env) args)

> instance Subst Fol where
>   apply env (R p args) = R p (map (apply env) args)

> instance (Subst a, Fv a) => Subst (Formula a) where
>   apply env (Atom a) = Atom(apply env a)
>   apply env (Not p) = Not(apply env p)
>   apply env (And p q) = apply env p /\ apply env q
>   apply env (Or p q) = apply env p \/ apply env q
>   apply env (Imp p q) = apply env p ==> apply env q
>   apply env (Iff p q) = apply env p <=> apply env q
>   apply env (Forall x p) = applyq env Forall x p
>   apply env (Exists x p) = applyq env Exists x p
>   apply _ Top = Top
>   apply _ Bot = Bot

Substitute under a binder
The following functions need the type variable, as they are used at multiple types

> variant :: Var -> Vars -> Var
> variant x vars = if List.elem x vars then variant (x ++ "'") vars else x

> applyq :: (Subst a, Fv a) => Env -> (Var -> Formula a -> Formula a) 
>        -> Var -> Formula a -> Formula a
> applyq env quant x p = quant x' (apply ((x |-> Var x') env) p)
>     where x' = if List.any (\k -> case Map.lookup k env of
>                                   Just v -> List.elem x (fv v)
>                                   Nothing -> False) (fv p \\ [x]) 
>                then variant x (fv(apply (Map.delete x env) p)) else x

> termval :: ([a], Var -> [b] -> b, Var -> [b] -> Bool) -> Map Var b -> Term -> b
> termval m@(_, func, _) v tm =
>   case tm of 
>     Var x -> case Map.lookup x v of
>                Nothing -> error "not in domain" 
>                Just y -> y
>     Fn f args -> func f (map (termval m v) args)

> holds :: ([a], Var -> [a] -> a, Var -> [a] -> Bool) -> Map Var a -> Formula Fol -> Bool
> holds m@(domain, _, pred) v fm =
>   case fm of 
>     Bot -> False
>     Top -> True
>     Atom (R r args) -> pred r (map (termval m v) args)
>     Not p -> not(holds m v p)
>     And p q -> holds m v p && holds m v q
>     Or p q -> holds m v p || holds m v q
>     Imp p q -> not (holds m v p )|| holds m v q
>     Iff p q -> holds m v p == holds m v q
>     Forall x p -> List.all (\a -> holds m (Map.insert x a v) p) domain
>     Exists x p -> List.any (\a -> holds m (Map.insert x a v) p) domain
