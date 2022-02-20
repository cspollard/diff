module Data.Real.Diff where

import Data.Real as ℝ
open ℝ using (ℝ)
open import Data.Real.Properties

import Data.Nat as ℕ
open ℕ using (ℕ; suc; zero; _⊓_; _⊔_)

open import Data.Unit.Polymorphic using (tt; ⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (_∘_)

-- TODO should move to _≈_ at some point
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning


open import Data.Vec hiding ([_])

module _ where
  open import Data.Vec.Recursive as VR

  [_] : ∀ {a} {A : Set a} {n} → A VR.^ n → Vec A n
  [_] {n = n} = VR.toVec n

Tower : ℕ → Set
Tower = Vec ℝ

const : ∀ {n} → ℝ → Tower n
const {zero} x = []
const {suc n} x = x ∷ const 0.0

return : ℝ → Tower 2
return x = x ∷ const 1.0

extract : Tower 1 → ℝ
extract = head

lop : ∀ {n} → Tower (suc n) → Tower n
lop {zero} _ = []
lop {suc n} (x ∷ xs) = x ∷ lop xs

apply : ∀ {n} (f : Tower 2 → Tower n) (x : ℝ) → Tower n
apply f = f ∘ return

run : (f : Tower 1 → Tower 1) (x : ℝ) → ℝ
run f = extract ∘ f ∘ const

diff : ∀ {n} → (f : Tower 2 → Tower (suc n)) → ℝ → Tower n
diff f = tail ∘ apply f

d^ : ∀ n (x : Tower (suc n)) → ℝ
d^ zero x = extract x
d^ (suc n) x = d^ n (tail x)

grad : (f : Tower 2 → Tower 2) → ℝ → ℝ
grad f = d^ 1 ∘ apply f

hessian : (f : Tower 2 → Tower 3) → ℝ → ℝ
hessian f = d^ 2 ∘ apply f


infixl 6 _+_
infixr 9 -_
_+_ : ∀ {n} → Tower n → Tower n → Tower n
-_ : ∀ {n} → Tower n → Tower n
[] + [] = []
(x ∷ xs) + (y ∷ ys) = x ℝ.+ y ∷ xs + ys
- [] = []
- (x ∷ xs) = ℝ.- x ∷ - xs

infixl 6 _-_
_-_ : ∀ {n} → Tower n → Tower n → Tower n
x - y = x + (- y)

infixl 7 _*_
_*_ : ∀ {n} → Tower n → Tower n → Tower n
[] * [] = []
xx@(x ∷ xs) * yy@(y ∷ ys) = x ℝ.* y ∷ lop xx * ys + lop yy * xs

_>-<_ : (ℝ → ℝ) → (∀ {m} → Tower m → Tower m) → ∀ {n} → Tower n → Tower n
(f >-< g) {zero} [] = []
(f >-< g) {suc n} xx@(x ∷ xs) = f x ∷ xs * g (lop xx)

infixl 8 _^^_
_^^_ : ∀ {n} → Tower n → (m : ℕ) → Tower n
x ^^ zero = const 1.0
x ^^ (suc n) = x * x ^^ n


infixr 9 e^_
e^_ : ∀ {n} → Tower n → Tower n
e^ [] = []
e^_ {suc n} xx@(x ∷ xs) = ℝ.e^ x ∷ xs * (e^ lop xx)

log recip sin cos sinh cosh abs sgn : ∀ {n} → Tower n → Tower n
log = ℝ.log >-< recip

recip [] = []
recip xx@(x ∷ xs) = 1/x ∷ 1/xx
  where
    1/x = 1.0 ℝ.÷ x
    1/xx = recip (lop xx)

abs = ℝ.abs >-< sgn

sgn [] = []
sgn (x ∷ xs) = if does (0.0 ≤? x) then const 1.0 else const (ℝ.- 1.0)
  where
    open import Data.Bool using (if_then_else_)
    open import Data.Real.Order
    open import Relation.Nullary


-- I'm not sure why I have to write these by hand.
sin [] = []
sin xx@(x ∷ xs) = ℝ.sin x ∷ xs * cos (lop xx)

cos [] = []
cos xx@(x ∷ xs) = ℝ.cos x ∷ - xs * sin (lop xx)

sinh [] = []
sinh xx@(x ∷ xs) = ℝ.sinh x ∷ xs * cosh (lop xx)

cosh [] = []
cosh xx@(x ∷ xs) = ℝ.cosh x ∷ xs * sinh (lop xx)

infix 8 _**_
_**_ : ∀ {n} → (x y : Tower n) → Tower n
x ** y = e^ (y * log x)

infix 2 _!_
_!_ : (∀ {n} → Tower n) → ∀ m → Tower m 
x ! m = x {m}


descend : (f : Tower 2 → Tower 2) (δ : ℝ) (n : ℕ) (x : ℝ) → ℝ
descend f δ zero x = x
descend f δ (suc n) x = descend f δ n (x ℝ.- δ ℝ.* grad f x)

ascend : (f : Tower 2 → Tower 2) (δ : ℝ) (n : ℕ) (x : ℝ) → ℝ
ascend f δ zero x = x
ascend f δ (suc n) x = ascend f δ n (x ℝ.+ δ ℝ.* grad f x)


sterling : ℕ → ℝ
sterling n = n' ℝ.* ℝ.log n' ℝ.- n'
  where
    n' = ℝ.fromℕ n

-- neglecting the normalization term
logPoisson' : ∀ {n} → ℕ → Tower n → Tower n
logPoisson' k α = const k' * log α - α
  where
    k' = ℝ.fromℕ k

logPoisson : ∀ {n} → ℕ → Tower n → Tower n
logPoisson k α = logPoisson' k α - const (sterling k)

test : ℝ → ℝ
test = ascend (logPoisson' 10) 0.5 1000

testgrad : ℝ → ℝ
testgrad = grad (logPoisson' 10)
