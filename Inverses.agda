
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Inverses where
  Endo : Set → Set
  Endo X = X → X


  _left-inverse-of_ : {X : Set} → Endo X → Endo X → Set
  f left-inverse-of g = ∀ x → f (g x) ≡ x

  _right-inverse-of_ : {X : Set} → Endo X → Endo X → Set
  f right-inverse-of g = ∀ x → g (f x) ≡ x

  _inverse-of_ : {X : Set} → Endo X → Endo X → Set
  f inverse-of g = (f left-inverse-of g) × (f right-inverse-of g)

  -- Invertible(f) is a proof that f has both a left and right inverse
  -- and they are the same.
  Invertible : {X : Set} → (f : Endo X) → Set
  Invertible {X = X} f = Σ[ g ∶ Endo X ] g inverse-of f

  -- The relation f inverse-of g is a symmetric relation. In other words
  -- if (f inverse-of g) then (g inverse-of f)
  inverse-of-sym : {X : Set} → (f g : Endo X) → (σ : f inverse-of g) → (g inverse-of f)
  inverse-of-sym f g σ = (proj₂ σ) , (proj₁ σ)

  _∘_ : {X : Set} → Endo X → Endo X → Endo X
  f ∘ g = λ x → f (g x)

  -- Given a proof σ : Invertible f we can produce an element
  -- g such that σ' : (g inverse-of f)
  inv-elem : {X : Set} → (f : Endo X) → (σ : Invertible f) → Endo X
  inv-elem f σ = proj₁ σ

  -- Given a function f ∈ Endo(X) and a proof σ : Invertible f
  -- we can produce a proof τ : (g inverse-of f) for some g
  invertible⇒inverse-of : {X : Set} → (f : Endo X) → (σ : Invertible f) → ((inv-elem f σ) inverse-of f)
  invertible⇒inverse-of f σ = proj₂ σ


  -- Given f ∈ Endo(X) and σ = a proof that f is invertible..
  -- then we can produce g = f⁻¹
  inverse : {X : Set} → (f : Endo X) → (σ : Invertible f) → Endo X
  inverse f σ = proj₁ σ

  -- Notice that Sym(X) is not a collection of functions!
  -- It's more than that! It's a collection of functions and
  -- for each such function, a proof that it is invertible!
  Sym : (X : Set) → Set
  Sym X = Σ[ f ∶ Endo X ] (Invertible f)

  -- This is just the 'underlying' set for Sym(X). In other words
  -- it is the set of invertible elements of Endo(X) but we have
  -- 'forgotten' that they are invertible.
  sym-func : {X : Set} → (α : Sym X) → Endo X
  sym-func α = proj₁ α

  -- Given (f, σ) = a ∈ Sym(X) then we can produce σ
  -- where σ = a proof that f is invertible
  sym-invertible : {X : Set} → (α : Sym X) → Invertible (proj₁ α)
  sym-invertible α = proj₂ α

  -- Given (f, σ) = α ∈ Sym(X) then we can produce f⁻¹
  sym-inverse : {X : Set} → (α : Sym X) → Endo X
  sym-inverse α = inverse (sym-func α) (sym-invertible α)


--  inverse-of-sym f g σ = (proj₂ σ) , (proj₁ σ)

  -- Given a function f ∈ Endo(X) and a proof σ : Invertible f
  -- we can produce a pair β = (f⁻¹, τ) ∈ Sym(X) where τ
  -- is a proof that f⁻¹ is invertible
  invertible⇒inverse-of2 : {X : Set} → (f : Endo X) → (σ : Invertible f) → (Sym X)
  invertible⇒inverse-of2 f σ = (inverse f σ) , {! !}

  inverse-of-sym2 : {X : Set} → (f g : Endo X) → (σ : f inverse-of g) → (Invertible g)
  inverse-of-sym2 f g σ = let τ = (proj₂ σ) , (proj₁ σ) in
                              f , (inverse-of-sym g f τ)


  -- Given any α = (f, σ) ∈ Sym(X) we can produce a proof τ that f⁻¹ is invertible
  inv-invertible : {X : Set} → (α : Sym X) → (Invertible (sym-inverse α))
  inv-invertible α = let f = proj₁ α
                         g = sym-inverse α
                         σ = proj₂ α
                         τ = inverse-of-sym2 f g {! !} in
                         g , {! !}

  id : {X : Set} → Endo X
  id x = x




