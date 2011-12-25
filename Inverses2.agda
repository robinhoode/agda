{-# OPTIONS --universe-polymorphism #-}

open import Data.Product

-- open import Relation.Binary.PropositionalEquality


open import Algebra.FunctionProperties.Core

open import Relation.Binary.PropositionalEquality -- as PropEq
--  using (_≡_; _≢_; refl; sym; cong; cong₂)

open ≡-Reasoning
module Inverses2 where

  -- The identity function
  id : ∀ {a} {X : Set a} → Op₁ X
  id x = x

  _∘_ : ∀ {a} {X : Set a} → Op₁ X → Op₁ X → Op₁ X
  f ∘ g = λ x → f (g x)

  comp-right-assoc : ∀ {a} {X : Set a} → (f g h : Op₁ X) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  comp-right-assoc f g h = refl

  comp-left-assoc :  ∀ {a} {X : Set a} → (f g h : Op₁ X) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  comp-left-assoc f g h = refl

  _left-inverse-of_ : ∀ {a} {X : Set a} → Op₁ X → Op₁ X → Set _
  f left-inverse-of g = (f ∘ g) ≡ id

  _right-inverse-of_ : ∀ {a} {X : Set a} → Op₁ X → Op₁ X → Set _
  f right-inverse-of g = (g ∘ f) ≡ id

  _left-id-of_ : ∀ {a} {X : Set a} → Op₁ X → Op₁ X → Set _
  f left-id-of g = f ∘ g ≡ g

  _right-id-of_ : ∀ {a} {X : Set a} → Op₁ X → Op₁ X → Set _
  f right-id-of g = g ∘ f ≡ g

  left-id-all : ∀ {a} {X : Set a} → (f : Op₁ X) → (id left-id-of f)
  left-id-all f = refl

  right-id-all : ∀ {a} {X : Set a} → (f : Op₁ X) → (id right-id-of f)
  right-id-all f = refl

  -- Elements of Sym X are bijections on X
  record Sym {a} (X : Set a) : Set a where
    field
      -- The bijection, some element f : X → X
      bijection   : Op₁ X
      -- The inverse of the bijection f.
      inverse     : Op₁ X
      -- The proof that f is a left-inverse of f⁻¹
      σ₁          : bijection left-inverse-of inverse
      -- The proof that f is a right-inverse of f⁻¹
      σ₂          : bijection right-inverse-of inverse

  idX : ∀ {a} {X : Set a} → Sym X
  idX = record
    { bijection = id
    ; inverse   = id
    ; σ₁        = refl
    ; σ₂        = refl
    }

  inv : ∀ {a} {X : Set a} → Sym X → Sym X
  inv s =
    let f   = Sym.bijection s
        f⁻¹ = Sym.inverse   s
        π₁  = Sym.σ₁        s
        π₂  = Sym.σ₂        s
    in record
    { bijection = f⁻¹
    ; inverse   = f
    ; σ₁        = π₂
    ; σ₂        = π₁
    }

  _⊗_ : ∀ {a} {X : Set a} → Sym X → Sym X → Sym X
  s ⊗ t =
    let f        = Sym.bijection s
        f⁻¹      = Sym.inverse   s
        g        = Sym.bijection t
        g⁻¹      = Sym.inverse   t
        left-inv = begin
                   ((f ∘ g) ∘ (g⁻¹ ∘ f⁻¹)) ≡⟨ cong (λ x → x) (comp-right-assoc f g (g⁻¹ ∘ f⁻¹)) ⟩
                   (f ∘ (g ∘ (g⁻¹ ∘ f⁻¹))) ≡⟨ cong (λ x → f ∘ x) (comp-left-assoc g g⁻¹ f⁻¹) ⟩
                   (f ∘ ((g ∘ g⁻¹) ∘ f⁻¹)) ≡⟨ cong (λ x → f ∘ (x ∘ f⁻¹)) (Sym.σ₁ t)  ⟩
                   (f ∘ (id ∘ f⁻¹))        ≡⟨ cong (λ x → f ∘ x) (left-id-all f⁻¹) ⟩
                   (f ∘ f⁻¹)               ≡⟨ cong (λ x → x) (Sym.σ₁ s) ⟩
                   id                      ∎
        right-inv = begin
                   ((g⁻¹ ∘ f⁻¹) ∘ (f ∘ g)) ≡⟨ cong (λ x → x) (comp-right-assoc g⁻¹ f⁻¹ (f ∘ g)) ⟩
                   (g⁻¹ ∘ (f⁻¹ ∘ (f ∘ g))) ≡⟨ cong (λ x → g⁻¹ ∘ x) (comp-left-assoc f⁻¹ f g) ⟩
                   (g⁻¹ ∘ ((f⁻¹ ∘ f) ∘ g)) ≡⟨ cong (λ x → g⁻¹ ∘ (x ∘ g)) (Sym.σ₂ s) ⟩
                   (g⁻¹ ∘ (id ∘ g))        ≡⟨ cong (λ x → g⁻¹ ∘ x) (left-id-all g) ⟩
                   (g⁻¹ ∘ g)               ≡⟨ cong (λ x → x) (Sym.σ₂ t) ⟩
                   id                      ∎

    in record
    { bijection   = f ∘ g
    ; inverse     = g⁻¹ ∘ f⁻¹
    ; σ₁          = left-inv
    ; σ₂          = right-inv
    }

  open import Algebra.Structures

  sym-x-is-a-group : ∀ {c} {Y : Set c} → (IsGroup _≡_ _⊗_ idX  inv)
  sym-x-is-a-group = {! !}


