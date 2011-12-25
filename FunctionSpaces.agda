
{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module FunctionSpaces where

  open import Level

  open import Function renaming (_∘_ to _⟨∘⟩_)
  open import Function.Equality as F
    using (_⟶_; _⟨$⟩_)
  open import Function.Injection   as Inj  hiding (id; _∘_)
  open import Function.Surjection  as Surj hiding (id; _∘_)
  open import Function.Bijection hiding (id; _∘_)

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality -- defines ≡

  open ≡-Reasoning
  open import Data.Product

  open import Algebra.FunctionProperties.Core public

  _LeftInverse_ : ∀ {x₁ x₂} {X : Setoid x₁ x₂} → X ⟶ X → X ⟶ X → Set _
  _LeftInverse_ {X = X} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈ x
    where open Setoid X

  record EndoEpimorphism {x₁ x₂} (X : Setoid x₁ x₂) : Set (x₁ ⊔ x₂) where
    field
      on : X ⟶ X
      left-inverse : on LeftInverse on

  _∘_ : ∀ {x₁ x₂} {X : Setoid x₁ x₂} → EndoEpimorphism X → EndoEpimorphism X → EndoEpimorphism X
  f ∘ g = record
    {
      left-inverse = (f left-inverse g)
    } where open EndoEpimorphism

  RightInverse : ∀ {x₁ x₂} {X : Setoid x₁ x₂} (f g : X ⟶ X) → Set _
  RightInverse {X = X} f g = ∀ x → g ⟨$⟩ (f ⟨$⟩ x) ≈ x
    where open Setoid X

  record EndoMonomorphism {x₁ x₂} (X : Setoid x₁ x₂) : Set (x₁ ⊔ x₂) where
    field
      on : X ⟶ X
      right-inverse : (RightInverse on) on

  record Automorphism {x₁ x₂} (X : Setoid x₁ x₂) : Set (x₁ ⊔ x₂) where
    field
      on : X ⟶ X
      left-inverse : on LeftInverse on
      right-inverse : (RightInverse on) on



