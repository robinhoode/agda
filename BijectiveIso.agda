
module BijectiveIso where

open import Function

open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module Defs {A B : Set} where
  Injective : (A → B) → Set
  Injective f = ∀ x y → f x ≡ f y → x ≡ y

  Surjective : (A → B) → Set
  Surjective f = ∀ y → Σ[ x ∶ A ] f x ≡ y

  Bijective : (A → B) → Set
  Bijective f = Injective f × Surjective f

  Iso : (A → B) → (B → A) → Set
  Iso f g = (∀ x → g (f x) ≡ x) × (∀ y → f (g y) ≡ y)

  pseudo-inv : ∀{f} → Surjective f → B → A
  pseudo-inv sur y = proj₁ (sur y)

  pseudo-inv' : ∀{f} → Bijective f → B → A
  pseudo-inv' bi = pseudo-inv (proj₂ bi)

  bijective-iso : ∀ f → (bi : Bijective f) → Iso f (pseudo-inv' bi)
  bijective-iso f bi = lemma₁ , lemma₂
    where
    g = pseudo-inv' bi
    lemma₁ : ∀ x → g (f x) ≡ x
    lemma₁ x = proj₁ bi (g (f x)) x
                 (proj₂ (proj₂ bi (f x)))

    lemma₂ : ∀ y → f (g y) ≡ y
    lemma₂ y = proj₂ (proj₂ bi y)


  iso-bijective : ∀ f g → Iso f g → Bijective f
  iso-bijective f g iso = inj , sur
    where
    inj : ∀ x y → f x ≡ f y → x ≡ y
    inj x y eq = begin
                   x
                 ≡⟨ sym (proj₁ iso x) ⟩
                   g (f x)
                 ≡⟨ cong g eq ⟩
                   g (f y)
                 ≡⟨ proj₁ iso y ⟩
                   y
                 ∎

    sur : ∀ y → Σ[ x ∶ _ ] f x ≡ y
    sur y = g y , proj₂ iso y

