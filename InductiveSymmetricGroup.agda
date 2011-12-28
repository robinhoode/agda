{-# OPTIONS --universe-polymorphism #-}

open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset
open import Data.Vec

module InductiveSymmetricGroup  where

  -- An n-cycle is a vector of integers with no repeated elements
  record Cycle (n : ℕ) : Set where
    field
      σ : Vec (Fin n) n
      isPerm :


