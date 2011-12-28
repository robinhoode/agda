
{-# OPTIONS --universe-polymorphism #-}

module SymmetricGroupProperties where
  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; _≢_; refl; sym; cong; cong₂)

  import Algebra.FunctionProperties as P
  open P _≡_
  open import SymmetricGroup

  ⊗-assoc : Associative _⊗_
  ⊗-assoc = {! !}



  -- isSemigroup : IsSemigroup _≡_ _⊗_
  -- isSemigroup = record
  --   {
  --     isEquivalence = PropEq.isEquivalence
  --   ; assoc         = {! !}
  --   ; ∙-cong        = {! !}
  --   }

  -- isMonoid : IsMonoid _≡_ _⊗_ idX
  -- isMonoid = {! !}

  -- isGroup : IsGroup _≡_ _⊗_ idX inv
  -- isGroup = {! !}

