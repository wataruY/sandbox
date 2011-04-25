module AgdaBasics where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data ℕ : Set where
  zero : ℕ
  suc : (p : ℕ) -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
suc p + n = suc (p + n)

_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
suc p * n = n + (p * n)

_or_ : Bool -> Bool -> Bool
true or y = true
false or y = y

_and_ : Bool -> Bool -> Bool
true and y = false
false and y = y

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if_then_else_ true x y = x
if_then_else_ false x y = y

infixl 60 _*_
infixl 40 _+_
infixl 20 _or_
infix 5 if_then_else_


data [_] (A : Set) : Set where
  [] : [ A ]
  _::_ : (x : A) -> (xs : [ A ]) -> [ A ]
infixr 40 _::_

data Vec (A : Set) : ℕ -> Set where
  [] : Vec A zero
  _::_ : {n : ℕ} -> (x : A) -> (xs : Vec A n) -> Vec A (suc n)

vmap : {A B : Set}{n : ℕ} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Image_∋_ {A B : Set} (f : A -> B) : (y : B) -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set} (f : A -> B) (y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x

data Fin : ℕ -> Set where
  fzero : {n : ℕ} -> Fin (suc n)
  fsuc : {n : ℕ} -> (p : Fin n) -> Fin (suc n)

magic : {A : Set} -> Fin zero -> A
magic ()

_!_ : {n : ℕ}{A : Set} -> Vec A n -> Fin n -> A
[] ! ()
x :: _ ! fzero = x
_ :: xs ! fsuc p = xs ! p

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x → f (g x)
infixr 80 _∘_

tabulate : {n : ℕ}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero} g = []
tabulate {suc p} g = g fzero :: tabulate (g ∘ fsuc)

data ⊥ : Set where
record ⊤ : Set where

trivial : ⊤
trivial = _

isTrue : Bool -> Set
isTrue true = ⊤
isTrue false = ⊥


length : {A : Set} -> [ A ] -> ℕ
length [] = zero
length (_ :: xs) = suc (length xs)

data _≡_ {A : Set} (x : A) : A -> Set where
  ≡-refl : x ≡ x

data _≤_ : ℕ -> ℕ -> Set where
  zero-≤ : {n : ℕ} -> zero ≤ n
  ≤-suc : {m n : ℕ} -> (p : m ≤ n) -> suc m ≤ suc n

data _<_ : ℕ -> ℕ -> Set where
  <-suc : {m n : ℕ} -> (p : m < n) -> suc m < suc n

_≤b_ : ℕ -> ℕ -> Bool
zero ≤b n = true
suc p ≤b zero = false
suc m ≤b suc n = m ≤b n

≤-trans : {l m n : ℕ} -> l ≤ m -> m ≤ n -> l ≤ n
≤-trans zero-≤ q = zero-≤
≤-trans (≤-suc p) (≤-suc q) = ≤-suc (≤-trans p q)

min : (m n : ℕ) -> ℕ
min m n with m ≤b n
min m n | true = m
min m n | false = n

filter : {A : Set} -> (A -> Bool) -> [ A ] -> [ A ]
filter p [] = []
filter p (x :: xs) with p x 
filter p (x :: xs) | true = x :: filter p xs
filter p (x :: xs) | false = filter p xs