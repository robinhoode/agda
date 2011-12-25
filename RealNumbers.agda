

module RealNumbers where
  open import Data.Nat
  open import Data.Integer

  data ℚ : Set where
    _/_ : ℤ → ℤ → ℚ

