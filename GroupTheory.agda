
{-# OPTIONS --universe-polymorphism #-}

open import Algebra

module GroupTheory {g₁ g₂} (G : Group g₁ g₂) where

  open import Level

  open import Function hiding (_∘_)
  open import Function.Equality as F
    using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
  open import Function.Injection   as Inj  hiding (id; _∘_)
  open import Function.Surjection  as Surj hiding (id; _∘_)
--  open import Function.LeftInverse as Left hiding (id; _∘_)
  open import Function.Bijection hiding (id; _∘_)

  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality -- defines ≡

  open ≡-Reasoning
  open import Data.Product

  open import Algebra.FunctionProperties.Core public

  LeftInverse_ : ∀ {x₁ x₂} {X : Setoid x₁ x₂} → (X ⟶ X) → (X ⟶ X) → Set _
  LeftInverse_ {X = X} f g = ∀ x → f ⟨$⟩ (g ⟨$⟩ x) ≈ x
    where open Setoid X

--  RightInverse_ : ∀ {x₁ x₂}

  -- record EndoEpimorphism {x₁ x₂} {X : Setoid x₁ x₂} (on : X ⟶ X) : Set (x₁ ⊔ x₂) where
  --   field
  --     on : X ⟶ X
  --     right-inverse : RightInverse X


  record Automorphic {x₁ x₂} {X : Setoid x₁ x₂} (to : X ⟶ X) : Set (x₁ ⊔ x₂) where
    field
      injective  : Injective  to
      surjective : Surjective to

    open Surjective surjective public

    left-inverse-of : from LeftInverseOf to
    left-inverse-of x = injective (right-inverse-of (to ⟨$⟩ x))

  record Automorphism {x₁ x₂} (X : Setoid x₁ x₂) : Set (x₁ ⊔ x₂) where
    field
      to          : X ⟶ X
      automorphic : Automorphic to

    open Automorphic automorphic public

    injection : Injection X X
    injection = record
      { to        = to
      ; injective = injective
      }

    surjection : Surjection X X
    surjection = record
      { to         = to
      ; surjective = surjective
      }

    open Surjection surjection public using (equivalent; right-inverse)

    left-inverse : LeftInverse X X
    left-inverse = record
      { to              = to
      ; from            = from
      ; left-inverse-of = left-inverse-of
      }

  infixr 9 _∘_

  _∘_ : ∀ {x₁ x₂} {X : Setoid x₁ x₂} → Automorphism X → Automorphism X → Automorphism X
  _∘_ {X = X} f g = record
    { automorphic = record
      { injective  =  Injection.injective   (Inj._∘_  (injection f)  (injection g))
      ; surjective = Surjection.surjective (Surj._∘_ (surjection f) (surjection g))
      }
    } where open Automorphism
            open Setoid X

  inverse : ∀ {x₁ x₂} {X : Setoid x₁ x₂} → Automorphism X → Automorphism X
  inverse {X = X} f = record
    { automorphic = record
      { injective  = {! !}
      ; surjective = {! !}
      }
    } where open Automorphism
            open Setoid X