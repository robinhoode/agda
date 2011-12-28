
open import Relation.Binary hiding (Sym)
open import Level

module Definition {a l} (X : Set a) (≅ : Rel X l) where
  open import Algebra.FunctionProperties.Core

  open import FunctionSpaces as FS hiding (left-id; right-id)


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

  -- Alias method
  bij : Sym X ≅ → Op₁ X
  bij s = Sym.bijection s

  -- Alias method
  inv : Sym X ≅ → Op₁ X
  inv s = Sym.inverse s

  left-inv : (s : Sym X ≅) → (bij s) left-inverse-of (inv s)
  left-inv s = Sym.left-inverse s

  right-inv : (s : Sym X ≅) → (bij s) right-inverse-of (inv s)
  right-inv s = Sym.right-inverse s

  infix 4 _≈_

  _≈_ : (s t : Sym X ≅) → Set _
  _≈_ s t = (bij s) ≡ (bij t)


