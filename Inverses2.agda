{-# OPTIONS --universe-polymorphism #-}

open import Data.Product

-- open import Relation.Binary.PropositionalEquality


open import Algebra.FunctionProperties.Core
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality -- as PropEq
--  using (_≡_; _≢_; refl; sym; cong; cong₂)

open ≡-Reasoning
module Inverses2 {a} (X : Set a) where
