
First order formulas. 

The grammar of formulas is parameterized by the nonterminal
'Atom' of atoms.  This is instantiated by Prop and Fol in
later files.  It's nice to have it as a parameter, as we
could potentially have different kinds of terms.

F ::= F <=> F1 | F1
F1 ::= F1 ==> F2 | F2
F2 ::= F2 \/ F3 | F3 
F3 ::= F3 /\ F4 | A
A ::= false | true | ( F ) | ~ A | Q | Atom
Q ::= forall Vars . F | exists Vars . F
Vars ::= x | x Vars

> module Formulas ( Formula(Top, Bot, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
>                 , Clause
>                 , Clauses
>                 , Var 
>                 , Vars
>                 , Sym
>                   -- Combinators
>                 , onatoms
>                 , overatoms
>                 , atomUnion
>                   -- Util
>                 , opp
>                 , negative
>                 , positive
>                 , conjuncts
>                 , disjuncts
>                 , listConj
>                 , listDisj
>                 , listForall
>                 , listExists
>                 , destImp
>                 , unIff
>                   -- Infix connectives
>                 , (/\), (\/), (<=>), (==>)
>                ) where

> import Prelude
> import qualified List 
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJ((<+>), (<>)) 
> import Parse(ReadT, Parser)
> import qualified Parse
> import Print(PP)
> import qualified Print

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Formulas and clauses

> type Var = String
> type Vars = [Var]

We'll need this later for function and predicate symbols 

> type Sym = String

> data Formula a = Top                   
>                | Bot                   
>                | Atom a                
>                | Not (Formula a)       
>                | And (Formula a) (Formula a)  
>                | Or (Formula a) (Formula a)    
>                | Imp (Formula a) (Formula a)   
>                | Iff (Formula a) (Formula a)   
>                | Forall Var (Formula a) 
>                | Exists Var (Formula a) 
>                  deriving (Ord, Eq)

> type Clause a = [Formula a]
> type Clauses a = [Clause a]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Infix

> (/\) :: Formula a -> Formula a -> Formula a 
> (/\) = And

> (\/) :: Formula a -> Formula a -> Formula a 
> (\/) = Or

> (==>) :: Formula a -> Formula a -> Formula a 
> (==>) = Imp

> (<=>) :: Formula a -> Formula a -> Formula a 
> (<=>) = Iff

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Combinators

Map

> onatoms :: (a -> Formula a) -> Formula a -> Formula a
> onatoms f fm =
>     case fm of 
>       Top -> Top
>       Bot -> Bot
>       Atom a -> f a
>       Not p -> Not (onatoms f p)
>       Or p q -> Or (onatoms f p) (onatoms f q)
>       And p q -> And (onatoms f p) (onatoms f q)
>       Imp p q -> Imp (onatoms f p) (onatoms f q)
>       Iff p q -> Iff (onatoms f p) (onatoms f q)
>       Forall x p -> Forall x (onatoms f p)
>       Exists x p -> Exists x (onatoms f p)

Fold

> overatoms :: (a -> b -> b) -> Formula a -> b -> b
> overatoms f fm b = 
>     case fm of 
>       Atom a -> f a b
>       Not p -> over1 p
>       Or p q -> over2 p q
>       And p q -> over2 p q
>       Imp p q -> over2 p q
>       Iff p q -> over2 p q
>       Forall _x p -> over1 p
>       Exists _x p -> over1 p
>       _ -> b
>       where over1 p = overatoms f p b
>             over2 p q = overatoms f p (overatoms f q b)

Collect atoms

> atomUnion :: Eq b => (a -> [b]) -> Formula a -> [b]
> atomUnion f fm = List.nub (overatoms (\h t -> f(h) ++ t) fm [])

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Util

Make a big conjunction(disjunction resp.) from a list
listConj [a,b,c] --> a & b & c 

> listConj :: [Formula a] -> Formula a
> listConj [] = Top
> listConj l = foldr1 And l

> listDisj :: [Formula a] -> Formula a
> listDisj [] = Bot
> listDisj l = foldr1 Or l

Make a big forall (exists resp.) from a list
listForall [x,y,z] <<P(x,y,z)>> --> <<forall x y z. P(x,y,z)>>

> listForall :: Vars -> Formula a -> Formula a
> listForall xs b = foldr Forall b xs

> listExists :: Vars -> Formula a -> Formula a
> listExists xs b = foldr Exists b xs

> destImp :: Formula a -> (Formula a, Formula a)
> destImp (Imp a b) = (a, b)
> destImp _ = error "destImp"

Opposite of a formula (Harrison's 'negate')

(Note that Harrison's term 'negate' is not usable because it's used by
the Prelude.)

> opp :: Formula a -> Formula a
> opp (Not p) = p 
> opp p = Not p

Sign of a formula

> negative :: Formula a -> Bool
> negative (Not _) = True
> negative _ = False

> positive :: Formula a -> Bool
> positive = not . negative

> conjuncts :: Formula a -> [Formula a]
> conjuncts (And p q) = conjuncts p ++ conjuncts q
> conjuncts fm = [fm]

> disjuncts :: Formula a -> [Formula a]
> disjuncts (Or p q) = disjuncts p ++ disjuncts q
> disjuncts fm = [fm]

Remove occurrences of <=> 

> unIff :: Formula a -> Formula a
> unIff fm = case fm of
>   Iff p q -> let p' = unIff p
>                  q' = unIff q in
>              (p' ==> q') /\ (q' ==> p')
>   Not p -> Not (unIff p)
>   Or p q -> unIff p \/ unIff q
>   And p q -> unIff p /\ unIff q
>   Imp p q -> unIff p ==> unIff q
>   Forall x p -> Forall x (unIff p)
>   Exists x p -> Exists x (unIff p)
>   _ -> fm

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Parsing

Note that the Atom nonterminal is a parameter.  Depending
on the form, it can make the grammar hard to parse without
backtracking.  For instance, if Atom allows top level parentheses,
we can't parse using an LR(1) parser generator.  

F ::= F <=> F1 | F1
F1 ::= F1 ==> F2 | F2
F2 ::= F2 \/ F3 | F3 
F3 ::= F3 /\ F4 | A
A ::= false | true | ( F ) | ~ A | Q | Atom
Q ::= forall Vars . F | exists Vars . F
Vars ::= x | x Vars

> instance (ReadT a) => ReadT (Formula a) where
>   readt = parseFormula [] 

> parseFormula :: ReadT a => Vars -> Parser (Formula a)
> parseFormula vs = 
>   Parse.rightInfix "<=>" Iff 
>     (Parse.rightInfix "==>" Imp
>        (Parse.rightInfix "\\/" Or
>          (Parse.rightInfix "/\\" And
>            (parseAtomic vs))))

> parseQuant :: ReadT a => Vars -> (Var -> Formula a -> Formula a) 
>            -> Var -> Parser (Formula a)
> parseQuant vs qcon x inp = case inp of
>   [] -> error "Body of quantified term expected"
>   ".":rest -> do (e, rest') <- parseFormula vs rest 
>                  return (qcon x e, rest')
>   y:rest -> do (e, rest') <- parseQuant (y:vs) qcon y rest 
>                return (qcon x e, rest')

Note that in atomic formulas, when we see a '(', we first 
check the atom parser to see if it will succeed.  Otherwise
we parse the parenthesized block as a formula.  This backtracking
avoids the problem mentioned above with LR(1) parsing.

> parseAtomic :: ReadT a => Vars -> Parser (Formula a)
> parseAtomic vs inp = case inp of 
>    [] -> error "formula expected"
>    "false" : rest -> Just (Bot, rest)
>    "true" : rest -> Just (Top, rest)
>    "(" : rest -> 
>      case Parse.readt inp of 
>        Just (e, rest1) -> Just (Atom e, rest1)
>        _ -> Parse.bracketed (parseFormula vs) ")" rest
>    "~" : rest -> 
>      case parseAtomic vs rest of
>        Nothing -> Nothing
>        Just (e, rest1) -> Just (Not e, rest1)
>    "forall":x:rest -> parseQuant (x:vs) Forall x rest
>    "exists":x:rest -> parseQuant (x:vs) Exists x rest
>    _ -> case Parse.readt inp of
>           Nothing -> Nothing
>           Just (e, rest1) -> Just (Atom e, rest1)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Printing

> instance PP a => Show (Formula a) where
>      show e = (PP.renderStyle Print.ppStyle 
>                (PP.text "<<" <> ppForm 0 e <> PP.text ">>")) 

> instance PP a => PP (Formula a) where
>   pp = ppForm 0

> ppForm :: PP a => Int -> Formula a -> PP.Doc
> ppForm pr f = case f of 
>    Bot -> PP.text "false"
>    Top -> PP.text "true"
>    Atom m -> Print.pp m
>    Not p -> paren (pr > 10) 1 (ppPrefixFm 10) "~" p
>    And p q -> paren (pr > 8) 0 (ppInfixFm 8 "/\\") p q
>    Or p q -> paren (pr > 6) 0 (ppInfixFm 6 "\\/") p q
>    Imp p q -> paren (pr > 4) 0 (ppInfixFm 4 "==>") p q
>    Iff p q -> paren (pr > 2) 0 (ppInfixFm 2 "<=>") p q
>    Forall _ _ -> paren (pr > 0) 2 ppQuant "forall" (stripQuant f)
>    Exists _ _ -> paren (pr > 0) 2 ppQuant "exists" (stripQuant f)

> ppPrefixFm :: PP a => Int -> String -> Formula a -> PP.Doc
> ppPrefixFm pr sym p = PP.text sym <> ppForm (pr+1) p

> ppInfixFm :: PP a => Int -> String -> Formula a -> Formula a -> PP.Doc
> ppInfixFm pr sym p q = PP.sep[PP.hsep[ppForm (pr+1) p, PP.text sym], ppForm pr q] 

> ppQuant :: PP a => String -> (Vars, Formula a) -> PP.Doc
> ppQuant name (bvs, bod) = PP.text name <+> PP.sep (map PP.text bvs) 
>                           <> PP.text "." <+> ppForm 0 bod

> paren :: Bool -> Int -> (a -> b -> PP.Doc) -> a -> b -> PP.Doc
> paren p n f x y = let d = f x y in
>                   PP.nest n (if p then PP.parens d else d)

> stripQuant :: Formula a -> (Vars, Formula a)
> stripQuant (Forall x (yp @ (Forall _ _))) = let (xs,q) = stripQuant yp in (x:xs, q)
> stripQuant (Exists x (yp @ (Exists _ _))) = let (xs,q) = stripQuant yp in (x:xs, q)
> stripQuant (Forall x p) = ([x], p)
> stripQuant (Exists x p) = ([x], p)
> stripQuant fm = ([], fm)
