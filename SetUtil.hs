{-# LANGUAGE UnicodeSyntax #-}
module SetUtil where
import Data.Set
import Data.Set.Unicode
import Prelude.Unicode
import qualified Prelude
import Prelude hiding (map)

powerset ∷ (Ord a) ⇒ Set a → Set (Set a)
powerset s = fromList $ Prelude.map (fromList) (powerList $ toList s)

powerList ∷ [a] → [[a]]
powerList [] = [[]]
powerList (x:xs) = powerList xs ++ Prelude.map (x:) (powerList xs)

all ∷ (a → Bool) → Set a → Bool
all p = fold (∧) True . map p

any ∷ (a → Bool) → Set a → Bool
any p = fold (∨) False . map p