{-# OPTIONS --universe-polymorphism #-}

open import Relation.Binary hiding (Sym)
open import Level

module SymmetricGroup.Definition {a l} {X : Set a} {≅ : Rel X l} where
  open import Relation.Binary.PropositionalEquality as PropEq
  open import Algebra.FunctionProperties.Core
  open import SymmetricGroup.FunctionSpaces as FS hiding (left-id; right-id)

  open PropEq.≡-Reasoning

  -- Elements of Sym X are bijections on X
  record Sym {a l} (X : Set a) (≅ : Rel X l) : Set (a ⊔ l) where
    field
      -- The bijection, some element f : X → X
      bijection     : Op₁ X
      -- The inverse of the bijection f.
      inverse       : Op₁ X
      -- The proof that f is a left-inverse of f⁻¹
      left-inverse  : bijection left-inverse-of inverse
      -- The proof that f is a right-inverse of f⁻¹
      right-inverse : bijection right-inverse-of inverse

  -- Alias methods
  bij : Sym X ≅ → Op₁ X
  bij s = Sym.bijection s

  inv : Sym X ≅ → Op₁ X
  inv s = Sym.inverse s

  left-inv : (s : Sym X ≅) → (bij s) left-inverse-of (inv s)
  left-inv s = Sym.left-inverse s

  right-inv : (s : Sym X ≅) → (bij s) right-inverse-of (inv s)
  right-inv s = Sym.right-inverse s

  infix 4 _≈_

  _≈_ : (s t : Sym X ≅) → Set _
  _≈_ s t = (bij s) ≡ (bij t)

  -- Identity element
  ι : Sym X ≅
  ι = record
    { bijection     = id
    ; inverse       = id
    ; left-inverse  = refl
    ; right-inverse = refl
    }

  -- Inverse element
  _ˣ : Op₁ (Sym X ≅)
  s ˣ = record
    { bijection     = inv s
    ; inverse       = bij s
    ; left-inverse  = right-inv s
    ; right-inverse = left-inv s
    }

  infixl 6 _⊗_

  _⊗_ : Op₂ (Sym X ≅)
  s ⊗ t =
    let f        = bij s
        f⁻¹      = inv s
        σ₁       = left-inv s
        σ₂       = right-inv s
        g        = bij t
        g⁻¹      = inv t
        τ₁       = left-inv t
        τ₂       = right-inv t
        π₁       = begin
                   ((f ∘ g) ∘ (g⁻¹ ∘ f⁻¹)) ≡⟨ cong id (∘-right-assoc f g (g⁻¹ ∘ f⁻¹)) ⟩
                   (f ∘ (g ∘ (g⁻¹ ∘ f⁻¹))) ≡⟨ cong (λ x → f ∘ x) (∘-left-assoc g g⁻¹ f⁻¹) ⟩
                   (f ∘ ((g ∘ g⁻¹) ∘ f⁻¹)) ≡⟨ cong (λ x → f ∘ (x ∘ f⁻¹)) τ₁ ⟩
                   (f ∘ (id ∘ f⁻¹))        ≡⟨ cong (λ x → f ∘ x) (FS.left-id f⁻¹) ⟩
                   (f ∘ f⁻¹)               ≡⟨ cong id σ₁ ⟩
                   id                      ∎

        π₂       = begin
                   ((g⁻¹ ∘ f⁻¹) ∘ (f ∘ g)) ≡⟨ cong id (∘-right-assoc g⁻¹ f⁻¹ (f ∘ g)) ⟩
                   (g⁻¹ ∘ (f⁻¹ ∘ (f ∘ g))) ≡⟨ cong (λ x → g⁻¹ ∘ x) (∘-left-assoc f⁻¹ f g) ⟩
                   (g⁻¹ ∘ ((f⁻¹ ∘ f) ∘ g)) ≡⟨ cong (λ x → g⁻¹ ∘ (x ∘ g)) σ₂ ⟩
                   (g⁻¹ ∘ (id ∘ g))        ≡⟨ cong (λ x → g⁻¹ ∘ x) (FS.left-id g) ⟩
                   (g⁻¹ ∘ g)               ≡⟨ cong id τ₂ ⟩
                   id                      ∎

    in record
    { bijection     = f ∘ g
    ; inverse       = g⁻¹ ∘ f⁻¹
    ; left-inverse  = π₁
    ; right-inverse = π₂
    }
