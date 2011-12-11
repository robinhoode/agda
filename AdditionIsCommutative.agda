
module AdditionIsCommutative where -- And now associative!

  open import Data.Nat hiding ( _+_ ; _≤_ ) -- natural numbers
  open import Relation.Binary.PropositionalEquality -- defines ≡

  open ≡-Reasoning
  open import Data.Product

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  suc m + n = suc (m + n)

  +0 : (n : ℕ) → n + zero ≡ n
  +0 zero = refl
  +0 (suc n) = begin
               suc n + zero ≡⟨ cong suc (+0 n) ⟩
               suc n ∎

  0+ : (n : ℕ) → n ≡ n + zero
  0+ zero = refl
  0+ (suc n) = begin
               suc n ≡⟨ cong suc (0+ n) ⟩
               (suc n) + zero ∎

  +suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
  +suc zero n = refl
  +suc (suc m) n = begin
                   (suc m) + (suc n) ≡⟨ cong suc (+suc m n) ⟩
                   suc (suc (m + n)) ∎

  suc+ : (m n : ℕ) → suc (m + n) ≡ m + suc n
  suc+ zero n = refl
  suc+ (suc m) n = begin
                   suc ((suc m) + n) ≡⟨ cong suc (suc+ m n) ⟩
                   (suc m) + (suc n) ∎

  +-comm' : (m n : ℕ) → m + n ≡ n + m
  +-comm' m zero = +0 m
  +-comm' m (suc n) = begin
                      m + suc n ≡⟨ +suc m n ⟩
                      suc (m + n) ≡⟨ cong suc (+-comm' m n) ⟩
                      (suc n) + m ∎

  +-assoc : (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)

  +-assoc m zero zero = begin
                        (m + zero) + zero ≡⟨ +0 (m + zero) ⟩
                        m + zero ∎

  +-assoc m zero p = begin
                     (m + zero) + p ≡⟨ cong (λ x → x + p) (+0 m) ⟩
                     m + p ∎

  +-assoc m n zero = begin
                     (m + n) + zero ≡⟨ +0 (m + n) ⟩
                     m + n ≡⟨ cong (λ x → m + x) (0+ n) ⟩
                     m + (n + zero) ∎

  +-assoc m (suc n) (suc p) = begin
                              (m + suc n) + suc p     ≡⟨ cong (λ x → x + suc p) (+suc m n) ⟩
                              suc (m + n) + suc p     ≡⟨ cong suc (+suc (m + n) p) ⟩
                              suc (suc ((m + n) + p)) ≡⟨ cong (λ x → suc (suc x)) (+-assoc m n p) ⟩
                              suc (suc (m + (n + p))) ≡⟨ cong suc (suc+ m (n + p)) ⟩
                              suc (m + suc (n + p))   ≡⟨ suc+ m (suc (n + p)) ⟩
                              m + (suc (suc (n + p))) ≡⟨ cong (λ x → m + suc x) (suc+ n p) ⟩
                              m + (suc n + suc p)     ∎

