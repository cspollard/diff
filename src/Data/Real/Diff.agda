module Data.Real.Diff where

import Data.Real as ℝ
open ℝ using (ℝ)
open import Data.Real.Properties

import Data.Nat as ℕ
open ℕ using (ℕ; suc; zero; _⊓_; _⊔_)

open import Data.Unit.Polymorphic using (tt; ⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (_∘_; id)

-- TODO should move to _≈_ at some point
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning


import Data.Vec as V
open V using (Vec; []; _∷_) 

import Data.Vec.Recursive as VR
open VR using (_^_; 2+_)

open import Data.Fin using (Fin; zero; suc)

Tower : ℕ → Set
Tower = Vec ℝ

Diff : Set
Diff = ∀ {d n} → Tower d ^ n → Tower d ^ n

Diff2 : Set
Diff2 = ∀ {d n} → Tower d ^ n → Tower d ^ n → Tower d ^ n

-- utility function
infix 2 _!_
_!_ : (∀ {d'} → Tower d') → ∀ d → Tower d
x ! d = x {d}

lift : ∀ {n a} {A : Set a} → A → A ^ n
lift {n} x = VR.replicate n x

const' : ∀ {d} → ℝ → Tower d
const' {zero} x = []
const' {suc d} x = x ∷ (const' 0.0)

const : ∀ {n d} → ℝ ^ n → Tower d ^ n
const {n} = VR.map const' n

return' : ∀ {d} → ℝ → Tower (suc d)
return' x = x ∷ const' 1.0

return : ∀ {n d} → ℝ ^ n → Tower (suc d) ^ n
return {n} = VR.map return' n

extract : ∀ {d n} → Tower (suc d) ^ n → ℝ ^ n
extract {n = n} = VR.map V.head n

lop : ∀ {d} → Tower (suc d) → Tower d
lop {zero} _ = []
lop {suc d} (x ∷ xs) = x ∷ lop xs

apply : ∀ {c d m n} (f : Tower (suc c) ^ m → Tower d ^ n) (x : ℝ ^ m) → Tower d ^ n
apply f = f ∘ return

run : ∀ {m n} (f : Tower 1 ^ m → Tower 1 ^ n) (x : ℝ ^ m) → ℝ ^ n
run f = extract ∘ f ∘ const

-- directional derivative
du
  : ∀ {c d m n} (f : Tower c ^ m → Tower (suc d) ^ n)
  → Tower c ^ m → Tower d ^ n
du {n = n} f xs = VR.map V.tail n (f xs)

fins : ∀ n → Fin n ^ n
fins n = VR.tabulate n id

directions : ∀ {d n} → ℝ ^ n → (Tower (suc d) ^ n) ^ n
directions {d} {n} x = VR.map (λ i → go i x) n (fins n)
  where
    go : ∀ {m} → Fin m → ℝ ^ m → Tower (suc d) ^ m
    go {1} zero y = return y
    go {2+ m} zero (y , ys) = return y , const ys
    go {2+ m} (suc i) (y , ys) = const y , go i ys

-- this is all very likely very slow
-- it's running du m times...
jacobian grad : ∀ {m n} (f : Tower 2 ^ m → Tower 2 ^ n) → ℝ ^ m → (ℝ ^ n) ^ m
jacobian {m = m} f x = VR.map (extract ∘ du f) m (directions x)
grad = jacobian


d2u
  : ∀ {c d m n} (f : Tower c ^ m → Tower (suc (suc d)) ^ n)
  → Tower c ^ m → Tower d ^ n
d2u {n = n} f xs = VR.map (V.tail ∘ V.tail) n (f xs)

outerWith
  : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → (f : A → B → C) → ∀ {m} → A ^ m → ∀ {n} → B ^ n → (C ^ n) ^ m
outerWith f {m} rm {n} rn = VR.map (λ x → VR.map (f x) n rn) m rm

-- hessian
--   : ∀ {c d m n} (f : Tower (suc c) ^ m  → Tower (2+ suc d) ^ n)
--   → ℝ ^ m → ((ℝ ^ n) ^ m) ^ m
-- hessian {m = m} f x = outerWith (λ y z → d2u ) (directions x) (directions x)

-_ : Diff
-_ {n = n} = VR.map (V.map λ x → ℝ.- x) n

infixl 6 _+_ _-_
infixr 9 -_
_+_ _-_ : Diff2
_+_ {n = n} = VR.zipWith (V.zipWith ℝ._+_) n
x - y = x + (- y)

*T : ∀ {d} (x y : Tower d) → Tower d
*T [] _ = []
*T xx@(x ∷ xs) yy@(y ∷ ys) = x ℝ.* y ∷ *T (lop xx) ys + *T (lop yy) xs

infixl 7 _*_
_*_ : Diff2
_*_ {zero} {n} x _ = x
_*_ {suc d} {n} = VR.zipWith *T n

_>-<_ : (ℝ → ℝ) → (∀ {d'} → Tower d' → Tower d') → ∀ {d} → Tower d → Tower d
(f >-< g) {zero} [] = []
(f >-< g) {suc d} xx@(x ∷ xs) = f x ∷ xs * g (lop xx)

liftF : ∀ {d} (f : Tower d → Tower d) → ∀ {n} → Tower d ^ n → Tower d ^ n
liftF f {n} = VR.map f n

infixl 8 _^^_
_^^_ : ∀ {d n} → Tower d ^ n → (m : ℕ) → Tower d ^ n
x ^^ zero = lift (const 1.0)
x ^^ (suc d) = x * x ^^ d


module Single where
  infixr 9 e^_
  e^_ log recip sin cos sinh cosh abs sgn : ∀ {d} → Tower d → Tower d

  e^ [] = []
  e^_ {suc d} xx@(x ∷ xs) = ℝ.e^ x ∷ xs * (e^ lop xx)

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


infixr 9 e^_
e^_ log recip sin cos sinh cosh abs sgn : Diff
e^_ = liftF Single.e^_
log = liftF Single.log
recip = liftF Single.recip
abs = liftF Single.abs
sgn = liftF Single.sgn
sin = liftF Single.sin
cos = liftF Single.cos
sinh = liftF Single.sinh
cosh = liftF Single.cosh

infix 8 _**_
_**_ : Diff2
x ** y = e^ (y * log x)

ascend descend
  : ∀ {n} (f : Tower 2 ^ n → Tower 2) (δ : ℝ ^ n) (m : ℕ) (x : ℝ ^ n) → ℝ ^ n
ascend f δ zero x = x 
ascend {n = n} f δ (suc m) x = ascend f δ m (add x (mul δ (grad f x)))
  where
    add mul : (x y : ℝ ^ n) → ℝ ^ n
    add = VR.zipWith ℝ._+_ n
    mul = VR.zipWith ℝ._*_ n

descend f = ascend λ x → - f x

sterling : ℕ → ℝ
sterling n = n' ℝ.* ℝ.log n' ℝ.- n'
  where
    n' = ℝ.fromℕ n

logPoisson' logPoisson : ∀ {n} → ℕ ^ n → ∀ {d} → Tower d ^ n → Tower d ^ n

-- neglecting the normalization term
logPoisson' {n} k α = const k' * log α - α
  where
    k' = VR.map ℝ.fromℕ n k

logPoisson {n} k α = logPoisson' k α - const (VR.map sterling n k)

sum : ∀ {d n} → Tower d ^ n → Tower d
sum {d} {n} = VR.foldl (λ _ → Tower d) (const 0.0) id (λ _ x y → x + y) n
  where open import Function using (id)

binned : ∀ {d n} → ℕ ^ n → Tower d ^ n → Tower d
binned n = sum ∘ logPoisson' n

test : ∀ {n} → ℝ ^ n → ℝ ^ n
test = ascend (binned (lift 10)) (lift 1.0) 1000

testgrad : ∀ {n} → ℝ ^ n → ℝ ^ n
testgrad = grad (binned (lift 10))

test' : jacobian (λ where (x , y) → x * y) (1.0 , 1.0) ≡ (1.0 , 1.0)
test' = refl
