
> module Complex
>   where

> import Prelude 
> import qualified List
> import qualified Char
> import qualified ListSet
> import qualified Formulas as F
> import Formulas(Formula(..), (/\), (\/), (==>), (<=>), Vars, Var, Sym)
> import qualified Fol
> import Fol(Fol(R), Term(..))
> import qualified Skolem
> import qualified Qelim
> import qualified Order

> polyAdd :: Vars -> Term -> Term -> Term
> polyAdd vars pol1 pol2 = 
>   case (pol1, pol2) of 
>     
