> {-# LANGUAGE UnicodeSyntax #-}

> module Matroid where
> import Data.Set
> import Data.Set.Unicode
> import SetUtil
> import Prelude hiding (all, map)

A Matroid is a special type of family of sets over a base set E. So we define a type for such a thing.

> type SetFamily a = Set (Set a)

Axioms for the independent sets:
I1. The empty set is independent

> i1 ∷ (Ord a) ⇒ SetFamily a → Bool
> i1 xss = (∅) ∈ xss

I2. Subsets of independent sets are independent

> i2 ∷ (Ord a) ⇒ SetFamily a → Bool
> i2 xss = let
>     isI xs = xs ∈ xss
>     in all isI $
>        unions $
>        toList $
>        map powerset xss

I3. Smaller independent sets can be enlarged using an element from a larger independent set.