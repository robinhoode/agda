-- Hey.. okay

module AgdaBasics where

------------------------------------------------------------------
-- http://code.haskell.org/Agda/examples/Introduction/Basics.agda
------------------------------------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data False : Set where

data True  : Set where
  trivial : True

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

-----------------------------------------------------------------
-- http://www.lix.polytechnique.fr/~keller/Documents-recherche/Stage08/Parallel-substitution/Equality.agda
-----------------------------------------------------------------

module Equality where
  data _==_ {A : Set} : A -> A -> Set where
    refl : {a : A} -> (a == a)


-----------------------------------------------------------------
-- http://www.cs.nott.ac.uk/~nzl/Home_Page/Homepage_files/%5BNuo_Li%5D%5Bfinal_year%5DReport.pdf
-----------------------------------------------------------------

--
-- Newbie note: It seems that the best way to keep things from
-- crashing into each other, until, that is, you want to handle
-- them, is to put them into modules..
--

module Naturals where
--  open Equality renaming (_==_ to _=~_; refl to refl~)

  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero     + n = n
  (succ n) + m = succ (n + m)

  -- The predecessor of n
  pred : Nat -> Nat
  pred zero     = zero
  pred (succ n) = n

  -- The number '1'
  one : Nat
  one = succ zero

  -- Newb note: Defining equality is probably a shitty idea, due
  -- to the fact that syntatic equality does not carry any
  -- information as far as it's provenance.
  --
  -- But for now, we'll stick with the syntatic equality.
  --

  -- _==_ : Nat -> Nat -> Set
  -- (zero     == zero)     = True
  -- (zero     == (succ n)) = False
  -- ((succ n) == zero)     = False
  -- ((succ n) == (succ m)) = (n == m)

  -- Syntatic equality type
  data _==_ {A : Set}(x : A) : A -> Set where
    refl : x == x

  cong : {A B : Set} (f : A -> B) {x y : A} -> (x == y) -> (f x == f y)
  cong f refl = refl

  -- Reflexivity of equality
--  refl : (n : Nat) -> n == n
--  refl n  = {!! !}


  -- Zero is a right identity of (+)
  right-id : (n : Nat) -> (n + zero) == n
  right-id zero                          = refl
  right-id (succ n)                      = cong succ (right-id n)

  rhs-right-id : (n : Nat) -> n == (n + zero)
  rhs-right-id zero                      = refl
  rhs-right-id (succ n)                  = cong succ (rhs-right-id n)

  -- Zero is a left identity of (+)
  left-id : (n : Nat) -> (zero + n) == n
  left-id zero                           = refl
  left-id (succ n)                       = cong succ (left-id n)

  succ-plus-one : (n : Nat) -> (n + one) == (succ n)
  succ-plus-one zero                     = refl
  succ-plus-one (succ n)                 = cong succ (succ-plus-one n)

  plus-one-succ : (n : Nat) -> (succ n) == (n + one)
  plus-one-succ zero                     = refl
  plus-one-succ (succ n)                 = cong succ (plus-one-succ n)

  pull-out-n : (n m : Nat) -> (succ (n + m)) == (n + (succ m))
  pull-out-n zero zero = refl
  pull-out-n zero (succ n) = refl
  pull-out-n (succ n) zero = {! (plus-one-succ (succ n + zero))!}
  pull-out-n (succ n) (succ m) = {! refl!}

  -- Moving a '1' from the first to second argument
  succ-zero-n : (n : Nat) -> (n + one) == (zero + (succ n))
  succ-zero-n zero                       = refl
  succ-zero-n (succ n)                   = cong succ (succ-zero-n n)

  succ-zero-n2 : (n : Nat) -> (one + n) == (zero + (succ n))
  succ-zero-n2 zero                       = refl
  succ-zero-n2 (succ n)                   = cong succ (succ-zero-n2 n)

  +-zero-comm : (n : Nat) -> (n + zero) == (zero + n)
  +-zero-comm zero = refl
  +-zero-comm (succ n) = cong succ (+-zero-comm n)

  +-zero-comm2 : (n : Nat) -> (zero + n) == (n + zero)
  +-zero-comm2 zero = refl
  +-zero-comm2 (succ n) = cong succ (+-zero-comm2 n)

  move-succ : (n m : Nat) -> ((succ n) + m) == (n + (succ m))
  move-succ zero zero  = refl
  move-succ zero  n    = succ-zero-n2 n
  move-succ n zero     = {! refl (succ-zero-n n)!}
  move-succ n m        = {! plus-one-succ (n + m)!}

  +-comm : (n m : Nat) -> (n + m) == (m + n)
  +-comm zero zero                       =  +-zero-comm zero
  +-comm zero (succ m)                   =  +-zero-comm2 (succ m)
  +-comm (succ n) zero                   =  +-zero-comm (succ n)
  +-comm (succ n) (succ m)               = {! !}





