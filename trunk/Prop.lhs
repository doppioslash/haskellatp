
Propositional Logic.  Atomic propositions are simply
propositional variables.

> module Prop ( Prop(..)
>             , eval
>             , atoms
>             , apply
>             , distrib
>             , simplify
>             , simplify1
>             , truthtable
>             , unsatisfiable
>             , satisfiable
>             , dualize
>             , trivial
>             , tautology
>             , occurrences
>             , subsume
>             , nnf
>             , nenf
>             , simpcnf
>             , cnf
>             , purednf
>             , simpdnf
>             , dnf
>             , parse
>             ) where

> import Prelude 
> import qualified List 
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJ(($+$)) 
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified Lib 
> import qualified ListSet
> import qualified Formulas as F
> import Formulas(Formula(..), (/\), (\/), (<=>), Sym)
> import Parse(ReadT)
> import qualified Parse
> import Print(PP)
> import qualified Print

Propositions

> newtype Prop = P Sym
>             deriving (Eq, Ord)

> instance ReadT Prop where
>   readt (p : rest) | p /= "(" = Just (P p, rest)
>   readt _ = Nothing

> instance Show Prop where
>   show (P s) = s

> instance PP Prop where
>   pp (P s) = PP.text s

> parse :: String -> Formula Prop
> parse = Parse.makeParser (Parse.formulaBracket Parse.readt)

> apply :: Ord a => Map a (Formula a) -> Formula a -> Formula a
> apply env = F.onatoms (\p -> case Map.lookup p env of 
>                                Just p' -> p'
>                                Nothing -> Atom p)

Evaluate a formula in a mapping of variables to truth values.

> eval :: Formula a -> (a -> Bool) -> Bool
> eval fm v = case fm of
>   Bot -> False
>   Top -> True
>   Atom x -> v x
>   Not p -> not (eval p v)
>   And p q -> eval p v && eval q v
>   Or p q -> eval p v || eval q v
>   Imp p q -> not (eval p v) || (eval q v)
>   Iff p q -> eval p v == eval q v
>   _ -> error "quantifier in prop eval"

-- FIXME: 

:load Prop Fol
let f = Fol.parse "<<p /\\ q ==> q /\\ r>>"

eval f (\P"p" -> True 
         P"q" -> False 
         P"r" -> True)

eval <<p /\ q ==> q /\ r>>
     (function P"p" -> true | P"q" -> true | P"r" -> false);;
END_INTERACTIVE;;

Return all atoms in a formula.

> atoms :: Ord a => Formula a -> [a]
> atoms fm = List.sort (F.atomUnion (\x -> [x]) fm)

Valuation combinator.  

A valuation is a mapping from atoms to truth values.

> onallvaluations :: Eq a => ((a -> Bool) -> b) -> (b -> b -> b) 
>                      -> (a -> Bool) -> [a] -> b
> onallvaluations subfn comb v pvs = case pvs of
>   [] -> subfn v
>   p:ps -> let v' t q = if q == p then t else v q in
>           comb (onallvaluations subfn comb (v' False) ps)
>                (onallvaluations subfn comb (v' True) ps)
> 

Truthtables.

> truthtable :: (Show a, Ord a) => Formula a -> String
> truthtable fm = PP.renderStyle Print.ppStyle (truthtableDoc fm)
>     where
>     truthtableDoc fm' =
>         let pvs = atoms fm' 
>             width = foldr (max . length . show) 5 pvs + 1 
>             fixw s = s ++ replicate (width - length s) ' ' 
>             truthstring p = fixw (if p then "true" else "false") 
>             separator = replicate (width * length pvs + 9) '-' 
>             row v =
>                 let lis = map (truthstring . v) pvs 
>                     ans = truthstring(eval fm' v) in
>                     [lis ++ [ans]]
>             rows = onallvaluations row (++) (const False) pvs
>             rowStr r = let (lis, ans) = splitAt (length r - 1) r in
>                            (foldr (++) ("| " ++ head ans) lis)
>         in
>         PP.empty $+$
>         PP.text (foldr (\s t -> fixw(show s) ++ t) "| formula" pvs) $+$
>         PP.empty $+$
>         PP.text separator $+$
>         PP.empty $+$
>         PP.vcat (map (PP.text . rowStr) rows) $+$
>         PP.text separator $+$
>         PP.empty 

Tautologies

> tautology :: Ord a => Formula a -> Bool
> tautology fm = onallvaluations (eval fm) (&&) (const False) (atoms fm)

Satisfiability

> unsatisfiable :: Ord a => Formula a -> Bool
> unsatisfiable fm = tautology(Not fm)

> satisfiable :: Ord a => Formula a -> Bool
> satisfiable fm = not(unsatisfiable fm)

Duality

> dualize :: Ord a => Formula a -> Formula a 
> dualize fm = Not (subdualize fm)

> subdualize :: Ord a => Formula a -> Formula a 
> subdualize fm = case fm of
>   Bot -> Top
>   Top -> Bot
>   Atom _ -> fm
>   Not p -> Not (subdualize p)
>   And p q -> Or (subdualize p) (subdualize q)
>   Or p q -> And (subdualize p) (subdualize q)
>   _ -> error "Formula involves connectives ==> and <=>"

Simplification

> simplify :: Ord a => Formula a -> Formula a
> simplify fm = case fm of
>   Not p -> simplify1 (Not (simplify p))
>   And p q -> simplify1 (And (simplify p) (simplify q))
>   Or p q -> simplify1 (Or (simplify p) (simplify q))
>   Imp p q -> simplify1 (Imp (simplify p) (simplify q))
>   Iff p q -> simplify1 (Iff (simplify p) (simplify q))
>   _ -> fm

> simplify1 :: Ord a => Formula a -> Formula a
> simplify1 fm = case fm of
>   Not Bot -> Top
>   Not Top -> Bot
>   And Bot _ -> Bot
>   And _ Bot -> Bot
>   And Top q -> q
>   And p Top -> p
>   Or Bot q -> q
>   Or p Bot -> p
>   Or Top _ -> Top
>   Or _ Top -> Top
>   Imp Bot _ -> Top
>   Imp Top q -> q
>   Imp _ Top -> Top
>   Imp p Bot -> Not p
>   Iff Top q -> q
>   Iff p Top -> p
>   Iff Bot q -> Not q
>   Iff p Bot -> Not p
>   _ -> fm

Negation normal form

> nnf :: Ord a => Formula a -> Formula a 
> nnf = nnf' . simplify
>   where nnf' fm = case fm of 
>                   And p q -> nnf' p /\ nnf' q
>                   Or p q -> nnf' p \/ nnf' q
>                   Imp p q -> nnf' (Not p) \/ nnf' q
>                   Iff p q -> (nnf' p /\ nnf' q) \/ (nnf'(Not p) /\ nnf'(Not q))
>                   Not(Not p) -> nnf' p
>                   Not(And p q) ->  nnf'(Not p) \/ nnf'(Not q)
>                   Not(Or p q) -> nnf'(Not p) /\ nnf'(Not q)
>                   Not(Imp p q) -> nnf' p /\ nnf'(Not q)
>                   Not(Iff p q) -> (nnf' p /\ nnf'(Not q)) \/ (nnf'(Not p) /\ nnf' q)
>                   fm -> fm

> nenf :: Ord a => Formula a -> Formula a 
> nenf = nenf' . simplify 
>   where nenf' fm = case fm of
>                    Not(Not p) -> nenf' p
>                    Not(And p q) -> nenf'(Not p) \/ nenf'(Not q)
>                    Not(Or p q) -> nenf'(Not p) /\ nenf'(Not q)
>                    Not(Imp p q) -> nenf' p /\ nenf'(Not q)
>                    Not(Iff p q) -> nenf' p <=> nenf'(Not q)
>                    And p q -> nenf' p /\ nenf' q
>                    Or p q -> nenf' p \/ nenf' q
>                    Imp p q -> nenf'(Not p) \/ nenf' q
>                    Iff p q -> nenf' p <=> nenf' q
>                    _ -> fm

Positive and negative occurrances of atoms

> occurrences :: Ord a => a -> Formula a -> (Bool, Bool)
> occurrences x fm = case fm of
>   Atom y -> (x == y, False)
>   Not p ->
>       let (pos, neg) = occurrences x p in (neg, pos)
>   And p q ->
>       let (pos1, neg1) = occurrences x p
>           (pos2, neg2) = occurrences x q in
>       (pos1 || pos2, neg1 || neg2)
>   Or p q ->
>         let (pos1, neg1) = occurrences x p
>             (pos2, neg2) = occurrences x q in
>         (pos1 || pos2, neg1 || neg2)
>   Imp p q ->
>         let (pos1, neg1) = occurrences x p
>             (pos2, neg2) = occurrences x q in
>         (neg1 || pos2, pos1 || neg2)
>   Iff p q ->
>         let (pos1, neg1) = occurrences x p
>             (pos2, neg2) = occurrences x q in
>         if pos1 || pos2 || neg1 || neg2 then (True, True)
>         else (False, False)
>   _ -> (False, False)

Distribute clauses 

> distrib :: Ord a => [[Formula a]] -> [[Formula a]] -> [[Formula a]]
> distrib = Lib.allPairs ListSet.union 

Subsumption

> subsume :: Ord a => [[Formula a]] -> [[Formula a]]
> subsume cls =
>   filter (\cl -> not(any (\cl' -> ListSet.psubset cl' cl) cls)) cls

Disjunctive normal form

> dnf :: Ord a => Formula a -> Formula a 
> dnf fm = F.listDisj(map F.listConj (simpdnf fm))

> simpdnf :: Ord a => Formula a -> [[Formula a]]
> simpdnf Bot = []
> simpdnf Top = [[]]
> simpdnf fm = subsume (filter (not . trivial) (purednf(nnf fm)))

> purednf :: Ord a => Formula a -> [[Formula a]]
> purednf fm = case fm of
>   And p q -> distrib (purednf p) (purednf q)
>   Or p q -> ListSet.union (purednf p) (purednf q)
>   _ -> [[fm]]

> trivial :: Ord a => [Formula a] -> Bool
> trivial lits =
>     let (pos, neg) = List.partition F.positive lits in
>     ListSet.intersect pos (map F.opp neg) /= []

Conjunctive normal form

> cnf :: Ord a => Formula a -> Formula a 
> cnf fm = F.listConj(map F.listDisj (simpcnf fm))

> simpcnf :: Ord a => Formula a -> [[Formula a]]
> simpcnf Bot = [[]]
> simpcnf Top = []
> simpcnf fm = 
>   let cjs = filter (not . trivial) (purecnf $ nnf fm) in
>   filter (\c -> not $ any (\c' -> ListSet.psubset c' c) cjs) cjs             

> purecnf :: Ord a => Formula a -> [[Formula a]]
> purecnf fm = map (map F.opp) (purednf(nnf(Not fm)))

:module + Prop
cnf (read "p <=> (q <=> r)")

