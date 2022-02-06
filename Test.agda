module Test where

open import Algebra using (CommutativeRing; IsCommutativeRing)

open import Assume using (assume)
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)

import Data.Fin as F
open F using (Fin)

open import Relation.Binary using (Rel; Setoid; _Preserves_⟶_)
open import Function using (Inverse; _on_; _∘_; _|>_; id)

open import Algebra.Module using (Module)
module Mod = Module

open import Data.Product using (_,_; proj₂)

open import Algebra.Module.Construct.DirectProduct using () renaming (⟨module⟩ to ×-module)
open import Level using (_⊔_; Level; 0ℓ)
open import Data.Vec.Recursive
open import Algebra.Module.Vec.Recursive

-- private
--   variable
--     r ℓ m ℓm ma ℓma mb ℓmb mc ℓmc : Level

module _ {r ℓ} {CR : CommutativeRing r ℓ} where
  Module↔
    : ∀ {m ℓm} (M : Module CR m ℓm)
    → ∀ {a ℓa} {S : Setoid a ℓa}
    → (inv : Inverse S (Mod.≈ᴹ-setoid M))
    → Module CR a ℓm
  Module↔ M {S = S} inv =
    record
    { Carrierᴹ = A
    ; _≈ᴹ_ = _≈ᴹ_ on f
    ; _+ᴹ_ = λ x y → f⁻¹ (f x +ᴹ f y)
    ; _*ₗ_ = λ s x → f⁻¹ (s *ₗ f x)
    ; _*ᵣ_ = λ x s → f⁻¹ (f x *ᵣ s)
    ; 0ᴹ = f⁻¹ 0ᴹ
    ; -ᴹ_ = λ x → f⁻¹ (-ᴹ f x)
    ; isModule = assume
    }
    where
      open Setoid S renaming (Carrier to A)
      open Inverse inv
      open Module M


module _
  {r ℓ} {CR : CommutativeRing r ℓ}
  {m ℓm} (M : Module CR m ℓm) 
  where

  data D : ℕ → Set m where
    z : Mod.Carrierᴹ M → D zero
    d : ∀ {n} → (x : Mod.Carrierᴹ M) → (dxs : D n) → D (suc n)

  runD : ∀ {n} →  Mod.Carrierᴹ (M ^ᴹ suc n) → D n
  runD {zero} x = z x
  runD {suc n} (x , xs) = d x (runD xs)

  private
    unD : ∀ {n} → D n → Mod.Carrierᴹ (M ^ᴹ suc n)
    unD {zero} (z x) = x
    unD {suc n} (d x xs) = x , unD xs


  open import Relation.Binary using (Setoid)

  module _ (n : ℕ) where
    private
      M' = M ^ᴹ suc n
      module M' = Module M'

    D-setoid : Setoid _ _
    D-setoid = setoid M'.≈ᴹ-setoid unD
      where
        open import Relation.Binary.Construct.On

    D-inv : Inverse D-setoid (Mod.≈ᴹ-setoid M')
    D-inv =
      record
      { f = unD
      ; f⁻¹ = runD
      ; cong₁ = assume
      ; cong₂ = assume
      ; inverse = assume
      }
      where
        open import Relation.Binary.Construct.On

instance
  D-module
    : ∀ {r ℓ} {CR : CommutativeRing r ℓ}
    → ∀ {m ℓm} {M : Module CR m ℓm}
    → ∀ {n}
    → Module CR _ _
  D-module {M = M} {n = n} = Module↔ (M ^ᴹ suc n) (D-inv M n)

module _
  {r ℓ} {CR : CommutativeRing r ℓ}
  where


  extract : ∀ {m ℓm} {M : Module CR m ℓm} → D M zero → Mod.Carrierᴹ M
  extract (z x) = x

  diff : ∀ {m ℓm} {M : Module CR m ℓm} {n} → D M (suc n) → D M n
  diff (d _ x) = x

  konst _# : ∀ {m ℓm} {n} {M : Module CR m ℓm} (c : Mod.Carrierᴹ M) → D M n
  konst {n = zero} {M = M} c = z c
  konst {n = suc n} {M = M} c = d c (konst (Mod.0ᴹ M))
  x # = konst x

  run : ∀ {m ℓm} {M : Module CR m ℓm} {n ℓn} {N : Module CR n ℓn} → (D M zero → D N zero) → Mod.Carrierᴹ M → Mod.Carrierᴹ N
  run f x = f (konst x) |> extract

import Real as ℝ
open ℝ using (ℝ)

open import Data.Vec.Recursive

ℝ-isCommutativeRing : IsCommutativeRing ℝ._≈_ ℝ._+_ ℝ._*_ ℝ.-_ 0.0 1.0
ℝ-isCommutativeRing = assume

ℝ-commutativeRing : CommutativeRing 0ℓ 0ℓ
ℝ-commutativeRing = record { isCommutativeRing = ℝ-isCommutativeRing }

private
  ℝ-mod' : Module ℝ-commutativeRing 0ℓ 0ℓ
  ℝ-mod' = U.⟨module⟩
    where import Algebra.Module.Construct.TensorUnit as U

ℝ^ : ∀ n → Module ℝ-commutativeRing 0ℓ 0ℓ
ℝ^ n = ℝ-mod' ^ᴹ n

ℝ-mod : Module ℝ-commutativeRing 0ℓ 0ℓ
ℝ-mod = ℝ^ 1

instance
  ℝ-cr : CommutativeRing 0ℓ 0ℓ
  ℝ-cr = ℝ-commutativeRing

  ℝ^n : ∀ {n} → Module ℝ-cr 0ℓ 0ℓ
  ℝ^n {n} = ℝ^ n


id' : ∀ {rank n} (c : Mod.Carrierᴹ (ℝ^ rank)) → D (ℝ^ rank) n
id' {rank} {zero} c = z c
id' {rank} {suc n} c = d c (konst (replicate rank 1.0))

var : ∀ {rank n} (c : (ℝ ^ rank) ^ suc n) → D (ℝ^ rank) n
var {rank} {zero} c = z c
var {rank} {suc n} (c , cs) = d c (var cs)


dot : ∀ {n} (x y : ℝ ^ suc n) → ℝ
dot {zero} x y = x ℝ.* y
dot {suc n} (x , xs) (y , ys) = x ℝ.* y ℝ.+ dot xs ys


jacobian
  : ∀ {rank1 rank2}
    (let M1 = ℝ^ rank1)
    (let M2 = ℝ^ rank2)
  → (D M1 1 → D M2 1)
  → (x v : Mod.Carrierᴹ M1) → Mod.Carrierᴹ M2
jacobian f x v = f (var (x , v)) |> diff |> extract


ε : ∀ {rank} → Fin rank → ℝ ^ rank
ε {zero} n = _
ε {suc zero} _ = 1.0
ε {2+ rank} F.zero = 1.0 , Mod.0ᴹ (ℝ^ (suc rank))
ε {2+ rank} (F.suc n) = Mod.0ᴹ ℝ-mod , ε n


∇_[_]
  : ∀ {rank}
  → (D (ℝ^ rank) 1 → D (ℝ^ 1) 1) → ℝ ^ rank → ℝ ^ rank
∇_[_] {rank = rank} ϕ x = {!   !}
  where
    unitvecs : (ℝ ^ rank) ^ rank
    unitvecs = map ε rank (tabulate rank id)


hessian
  : ∀ {rank1 rank2}
    (let M1 = ℝ^ rank1)
    (let M2 = ℝ^ rank2)
  → (D M1 2 → D M2 2)
  → (x v v' : Mod.Carrierᴹ M1) → Mod.Carrierᴹ M2
hessian f x v v' = f (var (x , v , v')) |> diff |> diff |> extract


-- linear and bilinear forms
_*_ : ∀ {n} → (x y : D ℝ-mod n) → D ℝ-mod n
_+_ _-_ : ∀ {r ℓ} {CR : CommutativeRing r ℓ} {m ℓm} {{M : Module CR m ℓm}} (x y : Mod.Carrierᴹ M) → Mod.Carrierᴹ M


lop
  : ∀ {l r} {CR : CommutativeRing l r}
  → ∀ {m ℓ} {M : Module CR m ℓ}
  → ∀ {n} → D M (suc n) → D M n
lop (d x (z _)) = z x
lop {n = suc n} (d x xs) = d x (lop {n = n} xs)


-- convenience function
_>-<_
  : ∀ {n}
  → (f : ℝ → ℝ) (f' : ∀ {m} → D ℝ-mod m → D ℝ-mod m)
  → D ℝ-mod n → D ℝ-mod n
_>-<_ f _ (z x) = z (f x)
_>-<_ f f' dgx@(d gx g'x) = d (f gx) (g'x * f' (lop dgx))


infixl 6 _+_ _-_
infixl 7 _*_ _÷_
infixl 8 _**_
infixr 9 -_
infixr 9 e^_

open Module {{...}}


z x * z y = z (x ℝ.* y)
dfx@(d fx f'x) * dgy@(d gy g'y) =
  d (fx ℝ.* gy) (lop dfx * g'y + lop dgy * f'x)

x + y = x +ᴹ y
x - y = x +ᴹ (-ᴹ y)

-_ : ∀ {r ℓ} {CR : CommutativeRing r ℓ} {m ℓm} {{M : Module CR m ℓm}} (x : Mod.Carrierᴹ M) → Mod.Carrierᴹ M
-_ x = -ᴹ x

ℝ-sgn : ℝ → ℝ
ℝ-sgn x = if does (0.0 ℝ.≤? x) then 1.0 else ℝ.- 1.0
  where
    open import Data.Bool using (if_then_else_)
    open import Relation.Nullary using (does)

ℝ-abs : ℝ → ℝ
ℝ-abs x = x ℝ.* ℝ-sgn x


-- the first is the zero-order 
poly : ∀ {rank n} → ℝ ^ suc rank → D ℝ-mod n → D ℝ-mod n
poly {rank = zero} cs x = konst cs
poly {rank = suc rank} (c , cs) x = konst c + x * poly cs x


log e^_ recip abs sgn : ∀ {n} → D ℝ-mod n → D ℝ-mod n
log = ℝ.log >-< (recip ∘ abs)

recip (z x) = z (1.0 ℝ.÷ x)
recip dfx@(d fx f'x) = d (1.0 ℝ.÷ fx) (- (f'x * tmp * tmp))
  where
    tmp = recip (lop dfx)

abs = ℝ-abs >-< sgn

sgn = ℝ-sgn >-< λ _ → 0ᴹ

-- TERMINATION
e^ z x = z (ℝ.e^ x)
e^ dfx@(d fx f'x) = d (ℝ.e^ fx) (f'x * e^ (lop dfx))

-- -- TODO
-- -- this could have sharing and be more efficient.
-- e^_ = ℝ.e^_ >-< ℝ.e^_
-- recip x = e^ - log x

_÷_ _**_ : ∀ {n} (x y : D ℝ-mod n) → D ℝ-mod n
x ÷ y = x * recip x
x ** y = e^ y * log x


_! : ℕ → ℕ
0 ! = 1
1 ! = 1
sucn@(suc n) ! = sucn ℕ.* (n !)


sterling : ∀ {n} → ℕ → D ℝ-mod n
sterling {n} m = m' * log m' - m'
  where
    m' : D ℝ-mod n
    m' = ℝ.fromℕ m #


-- without the constant denominator term
logPoisson' : ∀ {n} → ℕ → D ℝ-mod n → D ℝ-mod n
logPoisson' k λ' = k' * log λ' - λ'
  where k' = ℝ.fromℕ k #

logPoisson : ∀ {n} → ℕ → D ℝ-mod n → D ℝ-mod n
logPoisson k λ' = logPoisson' k λ' - sterling k


descend : ∀ {rank} (f : D (ℝ^ rank) 1 → D ℝ-mod 1) (steps : ℕ) (start : ℝ ^ rank) → ℝ ^ rank
descend f zero start = start
descend f (suc steps) start = {!   !}


module _ where
  open import Relation.Binary.PropositionalEquality using (refl)

  _ : ∇ ((λ x → x +ᴹ x)) [ 1.0 ] ℝ.≈ 2.0
  _ = refl

  _ : run e^_ 2.0 ℝ.≈ (ℝ.e^ 2.0)
  _ = refl


  testpoly : ∀ {n} → D ℝ-mod n → D ℝ-mod n
  testpoly = poly (1.0 , 2.0 , 3.0)


  _ : run testpoly 2.0 ℝ.≈ (1.0 + 4.0 + 12.0)
  _ = refl

  _ : ∇ testpoly [ 2.0 ] ℝ.≈ (0.0 + 2.0 + 3.0 ℝ.* 2.0 ℝ.* 2.0)
  _ = refl

  _ : ∇ testpoly [ 7.0 ] ℝ.≈ (0.0 + 2.0 + 2.0 ℝ.* 3.0 ℝ.* 7.0)
  _ = refl

  _ : hessian e^_ 1.0 1.0 0.0 ℝ.≈ (ℝ.e^ 1.0)
  _ = refl

  asdf : D ℝ-mod 2
  asdf = e^ var (2.0 , 1.0 , 0.0)

  _ : hessian (poly (1.0 , 2.0 , 3.0)) 1.0 1.0 0.0 ℝ.≈ (2.0 ℝ.* 3.0)
  _ = refl

  _ : ∇ log [ 1.0 ] ℝ.≈ 1.0
  _ = refl

  _ : ∇ log [ -ᴹ 1.0 ] ℝ.≈ 1.0
  _ = refl

  _ : ∇ sgn [ 2.0 ] ℝ.≈ 0.0
  _ = refl

  _ : ∇ abs [ 2.0 ] ℝ.≈ 1.0
  _ = refl

  _ : run abs (- 2.0) ℝ.≈ 2.0
  _ = refl

  _ : ∇ abs [ - 1.0 ] ℝ.≈ (- 1.0)
  _ = refl

  _ : ∇ recip [ - 2.0 ] ℝ.≈ (- 0.25)
  _ = refl

  _ : ∇ log [ 2.0 ] ℝ.≈ 0.5
  _ = refl