
> module Test (empty)
> where

> newtype LList a = LList [a]



> empty :: LList a 
> empty = LList []

> ($) :: [a] -> LList a
> ($) = LList

-- > v :: LList Int
-- > v = LList [5]

