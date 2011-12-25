

module Injective where
  data ∃ {a : Set} (P : a → Set) : Set where
    _,_ : (x : a) (w : P x) → ∃ P

  data _≡_ {a : Set} (x : a) : a → Set where
    ≡-refl : x ≡ x

  ≡-trans : ∀{a} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
  ≡-trans ≡-refl ≡-refl = ≡-refl

  ≡-symm : ∀{a} {x y : a} → x ≡ y → y ≡ x
  ≡-symm ≡-refl = ≡-refl

  ≡-resp : ∀{a b} {x y : a} (f : a → b) → x ≡ y → f x ≡ f y
  ≡-resp f ≡-refl = ≡-refl

  injective : ∀ {a b} → (a → b) → Set
  injective f = ∀ {x y} → f x ≡ f y → x ≡ y

  surjective : ∀{a b} → (a → b) → Set
  surjective f = ∀ y → ∃ (λ x → y ≡ f x)

  data Image {a b : Set} (f : a → b) : Set where
    -- This is a relation..!
    -- It's job is nothing more than to 'pull out' the y in the image function below
    _⟶_⟨_⟩ : (x : a) (y : b) (eq : y ≡ f x) → Image f

  -- This is the inclusion map from Image(f) ↪ b
  image : ∀{a b} {f : a → b} → Image f → b
  image (_ ⟶ y ⟨ _ ⟩) = y

  agrees : ∀{a b} (f : a → b) (f' : a → Image f) → Set
  agrees f f' = ∀ x → f x ≡ image (f' x)


