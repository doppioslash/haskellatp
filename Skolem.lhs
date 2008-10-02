
> module Skolem ( simplify
>               , nnf
>               , prenex
>               , pnf
>               , specialize
>               , skolem
>               , skolemize
>               , askolemize
>               ) where

> import Prelude 
> import qualified List 
> import Lib((|=>))
> import Formulas(Formula(..), (\/), (/\), (==>), (<=>), Var, Vars, Sym)
> import qualified Formulas as F
> import qualified Prop 
> import Fol(Fol(..), Term(..))
> import qualified Fol

%%%%%%%%%%%%%%%%%%%%%
%%% Simplification

> simplify :: Formula Fol -> Formula Fol
> simplify (Not p) = simplify1 $ Not $ simplify p
> simplify (And p q) = simplify1 (simplify p /\ simplify q)
> simplify (Or p q) = simplify1 (simplify p \/ simplify q)
> simplify (Imp p q) = simplify1 (simplify p ==> simplify q)
> simplify (Iff p q) = simplify1 (simplify p <=> simplify q)
> simplify (Forall x p) = simplify1 $ Forall x (simplify p)
> simplify (Exists x p) = simplify1 $ Exists x (simplify p)
> simplify fm = fm

> simplify1 :: Formula Fol -> Formula Fol
> simplify1 fm = case fm of
>                Forall x p -> if List.elem x (Fol.fv p) then fm else p
>                Exists x p -> if List.elem x (Fol.fv p) then fm else p
>                _ -> Prop.simplify1 fm

%%%%%%%%%%%%%%%%%%%%%%%%
%%% Negation Normal Form

> nnf :: Formula a -> Formula a
> nnf (And p q) = And (nnf p) (nnf q)
> nnf (Or p q) = Or (nnf p) (nnf q)
> nnf (Imp p q) = Or (nnf (Not p)) (nnf q)
> nnf (Iff p q) = Or (And (nnf p) (nnf q)) (And (nnf(Not p)) (nnf(Not q)))
> nnf (Not(Not p)) = nnf p
> nnf (Not(And p q)) = Or (nnf(Not p)) (nnf(Not q))
> nnf (Not(Or p q)) = And (nnf(Not p)) (nnf(Not q))
> nnf (Not(Imp p q)) = And (nnf p) (nnf(Not q))
> nnf (Not(Iff p q)) = Or (And (nnf p) (nnf(Not q))) (And (nnf(Not p)) (nnf q))
> nnf (Forall x p) = Forall x (nnf p)
> nnf (Exists x p) = Exists x (nnf p)
> nnf (Not (Forall x p)) = Exists x (nnf (Not p))
> nnf (Not (Exists x p)) = Forall x (nnf (Not p))
> nnf fm = fm

nnf $ read "(forall x. P(x)) ==> ((exists y. Q(y)) <=> exists z. P(z) & Q(z))"

%%%%%%%%%%%%%%%%%%%%%%%
%%% Prenex Normal Form

> pnf :: Formula Fol -> Formula Fol
> pnf = prenex . nnf . simplify

> prenex :: Formula Fol -> Formula Fol
> prenex (Forall x p) = Forall x (prenex p)
> prenex (Exists x p) = Exists x (prenex p)
> prenex (And p q) = pullquants (prenex p /\ prenex q)
> prenex (Or p q) = pullquants (prenex p \/ prenex q)
> prenex fm = fm

> pullquants :: Formula Fol -> Formula Fol
> pullquants fm = case fm of
>   And (Forall x p) (Forall y q) -> 
>     pullq (True,True) fm Forall And x y p q
>   Or (Exists x p) (Exists y q) -> 
>     pullq (True,True) fm Exists Or x y p q
>   And (Forall x p) q -> pullq (True,False) fm Forall And x x p q
>   And p (Forall y q) -> pullq (False,True) fm Forall And y y p q
>   Or (Forall x p) q ->  pullq (True,False) fm Forall Or x x p q
>   Or p (Forall y q) ->  pullq (False,True) fm Forall Or y y p q
>   And (Exists x p) q -> pullq (True,False) fm Exists And x x p q
>   And p (Exists y q) -> pullq (False,True) fm Exists And y y p q
>   Or (Exists x p) q ->  pullq (True,False) fm Exists Or x x p q
>   Or p (Exists y q) ->  pullq (False,True) fm Exists Or y y p q
>   _ -> fm

> pullq :: (Bool, Bool) -> Formula Fol 
>       -> (Var -> Formula Fol -> Formula Fol) 
>       -> (Formula Fol -> Formula Fol -> Formula Fol) -> Var -> Var
>       -> Formula Fol -> Formula Fol -> Formula Fol
> pullq (l,r) fm quant op x y p q =
>   let z = Fol.variant x (Fol.fv fm) 
>       p' = if l then Fol.apply (x |=> Var z) p else p
>       q' = if r then Fol.apply (y |=> Var z) q else q in
>   quant z (pullquants(op p' q'))

(forall y. Q(y)) & (forall x. P(y))
(forall y. Q(y)) & (forall x. ~ P(y))

%%%%%%%%%%%%%%%%%
%%% Skolemization

> specialize :: Formula Fol -> Formula Fol 
> specialize (Forall _ p) = specialize p
> specialize fm = fm

> skolemize :: Formula Fol -> Formula Fol 
> skolemize = specialize . pnf . askolemize

> askolemize :: Formula Fol -> Formula Fol 
> askolemize fm = fst ((skolem $ nnf $ simplify fm) (map fst (Fol.functions fm)))

> skolem :: Formula Fol -> Vars -> (Formula Fol, [Sym])
> skolem fm fns = case fm of
>     Exists y p ->
>         let xs = Fol.fv(fm) 
>             f = Fol.variant (if xs == [] then "c_" ++ y else "f_" ++ y) fns 
>             fx = Fn f (map Var xs) in
>         skolem (Fol.apply (y |=> fx) p) (f:fns)
>     Forall x p -> let (p', fns') = skolem p fns in (Forall x p', fns')
>     And p q -> skolem2 And (p, q) fns
>     Or p q -> skolem2 Or (p, q) fns
>     _ -> (fm, fns)

> skolem2 :: (Formula Fol -> Formula Fol -> Formula Fol) -> (Formula Fol, Formula Fol) 
>         -> Vars -> (Formula Fol, [Sym])
> skolem2 cons (p,q) fns =
>   let (p', fns') = skolem p fns 
>       (q', fns'') = skolem q fns' in
>   (cons p' q', fns'')

skolemize $ read "exists y. x < y ==> forall u. exists v. x * u < y * v"
skolemize $ read "forall x. P(x) ==> (exists y z. Q(y) | ~(exists z. P(z) & Q(z)))"

