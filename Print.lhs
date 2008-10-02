
> module Print ( PP(pp)
>              , showLine
>              , ppList
>              , ppListVert
>              , ppMap
>              , ppStyle
>              , ppShow )
>   where

> import Prelude 
> import Text.PrettyPrint.HughesPJ(Doc, (<>), (<+>), ($+$))
> import qualified Text.PrettyPrint.HughesPJ as PP
> import qualified Data.Map as Map
> import Data.Map(Map)

> class PP a where
>   pp :: a -> Doc

> ppStyle :: PP.Style
> ppStyle = PP.Style PP.PageMode 80 1.5

> showLine :: Show a => a -> String
> showLine x = show x ++ "\n"

> ppList :: (a -> Doc) -> [a] -> Doc
> ppList f xs = PP.lparen <> PP.hsep (PP.punctuate (PP.comma <+> PP.empty) (map f xs)) <> PP.rparen

> vsep :: [Doc] -> Doc
> vsep = foldr ($+$) PP.empty 

> ppListVert :: (a -> Doc) -> [a] -> Doc
> ppListVert f xs = PP.lbrack <> vsep (PP.punctuate PP.comma (map f xs)) <> PP.rbrack

> ppMap :: (PP k, PP v) => Map k v -> Doc
> ppMap = ppListVert (\(v, k) -> pp k <+> PP.text ":" <+> pp v) . Map.toList 

> ppShow :: (a -> Doc) -> (a -> String)
> ppShow f = PP.renderStyle ppStyle . f
