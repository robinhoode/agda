--
-- This website has been an ENORMOUS help
--
-- http://www.cs.nott.ac.uk/~txa/g53cfr/
--

module Equality where
  Prp : Set₁
  Prp = Set

  _⇒_ : Prp → Prp → Prp
  P ⇒ Q = P → Q

  infixr 0 _⇒_


  --  "By definition" translates to "refl".

  data _≡_ {A : Set} : A → A → Prp where
    refl : {a : A} → a ≡ a

  infix 4 _≡_

  -- Symmetric and transitive properties of equality
  sym : {A : Set} → {a b : A} → a ≡ b ⇒ b ≡ a
  -- This should be read:
  --   If ≡ is reflexive, then by definition, it is
  --   symmetric
  sym refl = refl

  -- This should be read:
  --   If ≡ is reflexive, then, given any proposition
  --   that (a ≡ b) ⇒ (b ≡ c) then, by definition
  --   we know (a ≡ c)
  trans : {A : Set}{a b c : A} → (a ≡ b) ⇒ (b ≡ c) ⇒ (a ≡ c)
  trans p refl = p

  --
  -- "use commutativity to prove that f(x, g(a * b)) = f(x, g(b* a))"?
  --
  -- I use (cong (λ p -> f (x,  g (  p ) )) (comm* {a} {b}) )

  -- We can 'push equality' through a function
  cong : {A B : Set} → (f : A → B) → {a b : A} → a ≡ b ⇒ f a ≡ f b
  cong f refl = refl

  module Naturals where
    data Nat : Set where
      zero : Nat
      succ : Nat → Nat

    _+_ : Nat → Nat → Nat
    zero   + n = n
    succ n + m = succ (n + m)

    -- This could have been done with cong!!
    --
    -- +-proj₁ : {n m : Nat} → n + m → n
    -- +-proj₁ n m = n


    0+ : (n : Nat) → zero + n ≡ n
    0+ n = refl

    n+0=n : (n : Nat) → n + zero ≡ n
    n+0=n zero = refl
    n+0=n (succ n) = cong succ (n+0=n n)

    +succ : (n m : Nat) → succ n + m ≡ succ (n + m)
    +succ n m = refl

    succ+ : (m n : Nat) → m + succ n ≡ succ (m + n)
    succ+ zero n = refl
    succ+ (succ m) n = cong succ (succ+ m n)

    +-comm : (m n : Nat) → m + n ≡ n + m
    +-comm n zero     = n+0=n n
    +-comm m (succ n) = trans (succ+ m n) (cong succ (+-comm m n))


    +-assoc : (m n o : Nat) → (m + n) + o ≡ m + (n + o)
    +-assoc zero n o = refl
    +-assoc (succ m) n o = cong succ (+-assoc m n o)


