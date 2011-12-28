{-# OPTIONS --universe-polymorphism #-}

open import Data.Product

-- open import Relation.Binary.PropositionalEquality

open import Algebra.FunctionProperties.Core
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality -- as PropEq
--  using (_≡_; _≢_; refl; sym; cong; cong₂)

open ≡-Reasoning
module FunctionSpaces {a} {X : Set a} where

  -- The identity function
  id : Op₁ X
  id x = x

  _∘_ : Op₁ X → Op₁ X → Op₁ X
  f ∘ g = λ x → f (g x)

  ∘-right-assoc : (f g h : Op₁ X) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  ∘-right-assoc f g h = refl

  ∘-left-assoc : (f g h : Op₁ X) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  ∘-left-assoc f g h = refl

  _left-inverse-of_ : (f g : Op₁ X) → Set _
  f left-inverse-of g = (f ∘ g) ≡ id

  _right-inverse-of_ : Op₁ X → Op₁ X → Set _
  f right-inverse-of g = (g ∘ f) ≡ id

  _left-id-of_ : Op₁ X → Op₁ X → Set _
  f left-id-of g = f ∘ g ≡ g

  _right-id-of_ : Op₁ X → Op₁ X → Set _
  f right-id-of g = g ∘ f ≡ g

  left-id : (f : Op₁ X) → (id left-id-of f)
  left-id f = refl

  right-id : (f : Op₁ X) → (id right-id-of f)
  right-id f = refl

