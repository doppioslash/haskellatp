
> module TestFormulas( prop
>                    , fol
>                    , unify
>                    , equality
>                    , -- lookupFol
>                    ) where

> import qualified Parse
> import Prelude 
> import Prop(Prop)
> import Fol(Fol, Term)
> import qualified Fol
> import Formulas(Formula)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Propositional

> prop :: IO [(String, Formula Prop)]
> prop = return []

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% First order

> folParser :: String -> [(String, Formula Fol)]
> folParser = Parse.makeParser (Parse.many (Parse.pair (Parse.until ((==) ",")) Fol.parser))

> fol :: IO [(String, Formula Fol)]
> fol = do s <- readFile "formulas.txt"
>          return (folParser s)

-- > lookupFol :: String -> IO (Formula Fol)
-- > lookupFol s = do l <- fol 
-- >                  case List.lookup s l of
-- >                    Nothing -> error ("not found: " ++ s)
-- >                    Just x -> return x

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Unification

> unify :: IO [[(Term,Term)]]
> unify = return []

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Equality

> equality :: IO [(String, Formula Fol)]
> equality = return []
