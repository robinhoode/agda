{-# OPTIONS --universe-polymorphism #-}

open import Relation.Binary hiding (Sym)
open import Level
open import Data.Product

module SymmetricGroup {a l} (X : Set a) (≅ : Rel X l) where
  open import Relation.Binary.PropositionalEquality as PropEq

  open import Algebra.Structures
  open import Algebra.FunctionProperties.Core

  open PropEq.≡-Reasoning
  open import FunctionSpaces as FS hiding (left-id; right-id)

  open import SymmetricGroup.Definition

  -- A proof that if two elements s, t : Sym(X) are approximately
  -- equivalent, then their inverses are equivalent
  inv-equiv : (s t : Sym X ≅) → (γ : s ≈ t) → (inv s) ≡ (inv t)
  inv-equiv s t γ =
    let f   = bij s
        f⁻¹ = inv s
        σ₁  = left-inv s
        σ₂  = right-inv s
        g   = bij t
        g⁻¹ = inv t
        τ₁  = left-inv t
        τ₂  = right-inv t
    in
      begin
      f⁻¹ ∘ id         ≡⟨ cong (λ x → f⁻¹ ∘ x) (sym τ₁) ⟩
      (f⁻¹ ∘ g) ∘ g⁻¹  ≡⟨ cong (λ x → (f⁻¹ ∘ x) ∘ g⁻¹) (sym γ) ⟩
      (f⁻¹ ∘ f) ∘ g⁻¹  ≡⟨ cong (λ x → x ∘ g⁻¹) σ₂ ⟩
      g⁻¹              ∎

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
  s ˣ =
    let f   = bij s
        f⁻¹ = inv s
        σ₁  = left-inv  s
        σ₂  = right-inv s
    in record
    { bijection     = f⁻¹
    ; inverse       = f
    ; left-inverse  = σ₂
    ; right-inverse = σ₁
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


  ∘-dist-⊗ : (s t : Sym X ≅) → bij (s ⊗ t) ≡ (bij s) ∘ (bij t)
  ∘-dist-⊗ s t = refl

  ⊗-dist-∘ : (s t : Sym X ≅) → (bij s) ∘ (bij t) ≡ bij (s ⊗ t)
  ⊗-dist-∘ s t = refl

  import Algebra.FunctionProperties as FP
  open FP _≈_

  ι-left-id : LeftIdentity ι _⊗_
  ι-left-id s = begin
                bij (ι ⊗ s)       ≡⟨ cong (λ x → x) (∘-dist-⊗ ι s) ⟩
                id ∘ (bij s)      ≡⟨ cong (λ x → x) (FS.left-id (bij s)) ⟩
                (bij s)           ∎

  ι-right-id : RightIdentity ι _⊗_
  ι-right-id s = begin
                 bij (s ⊗ ι)       ≡⟨ cong id (∘-dist-⊗ s ι) ⟩
                 (bij s) ∘ id      ≡⟨ cong id (FS.right-id (bij s)) ⟩
                 (bij s)           ∎


--  ⊗-cong : _⊗_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ⊗-cong : {x y u v : Sym X ≅} → x ≈ y → u ≈ v → x ⊗ u ≈ y ⊗ v
  ⊗-cong {x} {y} {u} {v} α β = begin
                               bij (x ⊗ u)       ≡⟨ refl ⟩
                               (bij x) ∘ (bij u) ≡⟨ cong (λ a → a ∘ (bij u)) α ⟩
                               (bij y) ∘ (bij u) ≡⟨ cong (λ a → (bij y) ∘ a) β ⟩
                               (bij y) ∘ (bij v) ≡⟨ cong id (⊗-dist-∘ y v) ⟩
                               bij (y ⊗ v)       ∎

  ⊗-assoc : Associative _⊗_
  ⊗-assoc x y z = begin
                  bij ((x ⊗ y) ⊗ z)             ≡⟨ cong id (∘-dist-⊗ (x ⊗ y) z) ⟩
                  (bij (x ⊗ y)) ∘ (bij z)       ≡⟨ cong (λ a → a ∘ (bij z)) (∘-dist-⊗ x y) ⟩
                  ((bij x) ∘ (bij y)) ∘ (bij z) ≡⟨ cong id (∘-right-assoc (bij x) (bij y) (bij z)) ⟩
                  (bij x) ∘ ((bij y) ∘ (bij z)) ≡⟨ cong (λ a → (bij x) ∘ a) (⊗-dist-∘ y z) ⟩
                  (bij x) ∘ (bij (y ⊗ z))       ≡⟨ cong id (⊗-dist-∘ x (y ⊗ z)) ⟩
                  bij (x ⊗ (y ⊗ z))             ∎

  ˣ-right-inv : RightInverse ι _ˣ _⊗_
  ˣ-right-inv s = begin
                  bij (s ⊗ (s ˣ))        ≡⟨ cong id (∘-dist-⊗ s (s ˣ)) ⟩
                  (bij s) ∘ (bij (s ˣ))  ≡⟨ cong id (left-inv s) ⟩
                  id                     ∎

  ˣ-left-inv : LeftInverse ι _ˣ _⊗_
  ˣ-left-inv s = begin
                 bij ((s ˣ) ⊗ s)       ≡⟨ cong id (∘-dist-⊗ (s ˣ) s) ⟩
                 (bij (s ˣ)) ∘ (bij s) ≡⟨ cong id (right-inv s) ⟩
                 id                    ∎



  ≈-equiv : IsEquivalence _≈_
  ≈-equiv = record
    {
      refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  SymX-is-a-Semigroup : IsSemigroup _≈_ _⊗_
  SymX-is-a-Semigroup = record
    {
      isEquivalence = ≈-equiv
    ; assoc         = ⊗-assoc
    ; ∙-cong        = ⊗-cong
    }

  SymX-is-a-Monoid : IsMonoid _≈_ _⊗_ ι
  SymX-is-a-Monoid = record
    {
      isSemigroup = SymX-is-a-Semigroup
    ; identity    = ι-left-id , ι-right-id
    }

  SymX-is-a-Group : IsGroup _≈_ _⊗_ ι _ˣ
  SymX-is-a-Group = record
    {
      isMonoid = SymX-is-a-Monoid
    ; inverse  = ˣ-left-inv , ˣ-right-inv
    ; ⁻¹-cong  = {! !}
    }

  -- TODO: Sym X is a Group (Cayley's Theorem)
  -- TODO: We have the cannonical G ↪ Sym G (Cayley's Embedding)
  --
  -- TODO: Subgroups!
  -- TODO: Langrange's Theorem!
  -- TODO: Normal subgroups!
  -- TODO: Quotient groups!
  -- ...
  -- ...
  -- TODO: Isomorphism Theorems!
  -- ...
  -- ...
  -- TODO: Sylow's Theorems!

