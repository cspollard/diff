module Test where

open import Algebra using (CommutativeRing; IsCommutativeRing)

open import Assume using (assume)
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)

import Data.Fin as F
open F using (Fin)

open import Relation.Binary using (Rel; Setoid; _Preserves_⟶_)
open import Function using (Inverse; _on_; _∘_; _|>_; id; flip)

open import Algebra.Module using (Module)
module Mod = Module

open import Data.Product using (_,_; proj₂; _×_)

open import Algebra.Module.Construct.DirectProduct using () renaming (⟨module⟩ to ×-module)
open import Level using (_⊔_; Level; 0ℓ; Lift)
open import Data.Vec.Recursive
open import Algebra.Module.Vec.Recursive


module _
  {r ℓ} {CR : CommutativeRing r ℓ}
  {m ℓm} (M : Module CR m ℓm)
  {n ℓn} (N : Module CR n ℓn)
  where

  private
    module M = Module M
    module N = Module N

  -- TODO
  -- can we use M → D N k everywhere?!
  data D : ℕ → Set (m ⊔ n) where
    z : N.Carrierᴹ → D zero
    d : ∀ {k} → (fx : N.Carrierᴹ) → (dfx : M.Carrierᴹ → D k) → D (suc k)


module _
  {r ℓ} {CR : CommutativeRing r ℓ}
  {m ℓm} {M : Module CR m ℓm}
  {n ℓn} {N : Module CR n ℓn}
  where

  private
    module CR = CommutativeRing CR
    module M = Module M
    module N = Module N

  private
    module dmod where

      Carrierᴹ : ∀ {k : ℕ} → Set (m ⊔ n)
      Carrierᴹ {k} = D M N k

      _≈ᴹ_ : ∀ {k} → Rel (D M N k) (m ⊔ ℓn)
      _≈ᴹ_ (z x) (z y) = Lift (m ⊔ ℓn) (x N.≈ᴹ y)
      _≈ᴹ_ (d fx dfx) (d fy dfy) = (fx N.≈ᴹ fy) × (∀ v → dfx v ≈ᴹ dfy v)

      _+ᴹ_ : ∀ {k} → (x y : D M N k) → D M N k
      _+ᴹ_ (z x) (z y) = z (x N.+ᴹ y)
      _+ᴹ_ (d fx dfx) (d fy dfy) = d (fx N.+ᴹ fy) λ v → dfx v +ᴹ dfy v

      _*ₗ_ : ∀ {k} → (s : CR.Carrier) (x : D M N k) → D M N k
      _*ₗ_ s (z x) = z (s N.*ₗ x)
      _*ₗ_ s (d fx dfx) = d (s N.*ₗ fx) λ v → s *ₗ dfx v

      _*ᵣ_ : ∀ {k} → (x : D M N k) (s : CR.Carrier) → D M N k
      _*ᵣ_ = flip _*ₗ_

      0ᴹ : ∀ {k} → D M N k
      0ᴹ {zero} = z N.0ᴹ
      0ᴹ {suc k} = d N.0ᴹ λ v → 0ᴹ

      -ᴹ_ : ∀ {k} → D M N k → D M N k
      -ᴹ_ (z x) = z (N.-ᴹ x)
      -ᴹ_ (d fx dfx) = d (N.-ᴹ fx) λ v → -ᴹ dfx v

  instance
    D-module : ∀ {k : ℕ} → Module CR _ _
    D-module {k} =
      record
      { Carrierᴹ = dmod.Carrierᴹ {k}
      ; isModule = assume
      ; dmod
      }

  private variable k : ℕ

  run : D M N k → N.Carrierᴹ
  run (z x) = x
  run (d x _) = x

  extract : D M N zero → N.Carrierᴹ
  extract = run

  diff : M.Carrierᴹ → D M N (suc k) → D M N k
  diff v (d _ x) = x v

  konst _# : ∀ (c : N.Carrierᴹ) → D M N k
  konst {k = zero} c = z c
  konst {k = suc k} c = d c (λ v → konst N.0ᴹ)
  x # = konst x

  jacobian : (df : D M N 1) (v : M.Carrierᴹ) → N.Carrierᴹ
  jacobian df v = df |> diff v |> extract

  hessian : (df : D M N 2) (v v' : M.Carrierᴹ) → N.Carrierᴹ
  hessian df v v' = df |> diff v |> diff v' |> extract

  hack : ∀ {l} → D M N (suc l) → D M N l
  hack {zero} (d fx dfx) = z fx
  hack {suc l} (d fx dfx) = d fx λ v → hack {l} (dfx v)


module _ where
  import Real as ℝ
  open ℝ using (ℝ)

  open import Data.Vec.Recursive

  ℝ-isCommutativeRing : IsCommutativeRing ℝ._≈_ ℝ._+_ ℝ._*_ ℝ.-_ 0.0 1.0
  ℝ-isCommutativeRing = assume

  instance
    ℝ-commutativeRing : CommutativeRing 0ℓ 0ℓ
    ℝ-commutativeRing = record { isCommutativeRing = ℝ-isCommutativeRing }

  ℝ-cr : CommutativeRing 0ℓ 0ℓ
  ℝ-cr = ℝ-commutativeRing

  private
    ℝ-mod' : Module ℝ-commutativeRing 0ℓ 0ℓ
    ℝ-mod' = U.⟨module⟩
      where import Algebra.Module.Construct.TensorUnit as U

  ℝ^ : ∀ n → Module ℝ-commutativeRing 0ℓ 0ℓ
  ℝ^ n = ℝ-mod' ^ᴹ n

  ℝ-mod : Module ℝ-commutativeRing 0ℓ 0ℓ
  ℝ-mod = ℝ^ 1

  -- TODO
  -- is this really the identity?
  var : ∀ {rank k} (c : Mod.Carrierᴹ (ℝ^ rank)) → D (ℝ^ rank) (ℝ^ rank) k
  var {rank} {zero} c = z c
  var {rank} {suc n} c = d c (λ v → konst (replicate rank 1.0))

  instance
    ℝ^n : ∀ {n} → Module ℝ-cr 0ℓ 0ℓ
    ℝ^n {n} = ℝ^ n


  infixl 6 _+_ _-_
  infixl 7 _*_
  -- linear and bilinear forms
  _*_
    : ∀ {m ℓm} {M : Module ℝ-cr m ℓm} {k rank}
    → (x y : D M (ℝ^ rank) k)
    → D M (ℝ^ rank) k

  open Module {{...}}
  _+_ _-_
    : ∀ {r ℓ} {CR : CommutativeRing r ℓ} {m ℓm} {{M : Module CR m ℓm}} (x y : Mod.Carrierᴹ M)
    → Mod.Carrierᴹ M
  x + y = x +ᴹ y
  x - y = x +ᴹ (-ᴹ y)


  _*_ {rank = rank} (z x) (z y) = z (zipWith ℝ._*_ rank x y)
  _*_ {rank = rank} dfx@(d fx f'x) dgx@(d gx g'x) =
    d (zipWith ℝ._*_ rank fx gx) (λ v → hack dfx * g'x v + hack dgx * f'x v)


  -- convenience function
  _>-<_
    : ∀ {k}
    → (f : ℝ → ℝ) (f' : ∀ {l} → D ℝ-mod ℝ-mod l → D ℝ-mod ℝ-mod l)
    → D ℝ-mod ℝ-mod k → D ℝ-mod ℝ-mod k
  (f >-< _) (z x) = z (f x)
  (f >-< f') dfx@(d x dx) = d (f x) λ v → dx v * f' (hack dfx)


  ε : ∀ {rank} → Fin rank → ℝ ^ rank
  ε {zero} n = _
  ε {suc zero} _ = 1.0
  ε {2+ rank} F.zero = 1.0 , Mod.0ᴹ (ℝ^ (suc rank))
  ε {2+ rank} (F.suc n) = Mod.0ᴹ ℝ-mod , ε n


  ∇_ grad : ∀ {rank} → D (ℝ^ rank) (ℝ^ 1) 1 → ℝ ^ rank
  ∇_ {rank = rank} f = map (jacobian f) rank unitvecs
    where
      unitvecs : (ℝ ^ rank) ^ rank
      unitvecs = map ε rank (tabulate rank id)

  grad = ∇_


  infixl 8 _**_
  infixr 9 -_
  infixr 9 e^_

  -_
    : ∀ {r ℓ} {CR : CommutativeRing r ℓ} {m ℓm} {{M : Module CR m ℓm}} (x : Mod.Carrierᴹ M)
    → Mod.Carrierᴹ M
  -_ x = -ᴹ x


  ℝ-sgn : ℝ → ℝ
  ℝ-sgn x = if does (0.0 ℝ.≤? x) then 1.0 else ℝ.- 1.0
    where
      open import Data.Bool using (if_then_else_)
      open import Relation.Nullary using (does)

  ℝ-abs : ℝ → ℝ
  ℝ-abs x = x ℝ.* ℝ-sgn x


  -- the first is the zero-order 
  poly : ∀ {rank k} → ℝ ^ suc rank → D ℝ-mod ℝ-mod k → D ℝ-mod ℝ-mod k
  poly {rank = zero} cs x = konst cs
  poly {rank = suc rank} (c , cs) x = konst c + x * poly cs x

  pow : ℕ → ∀ {k} → D ℝ-mod ℝ-mod k → D ℝ-mod ℝ-mod k
  pow 0 x = konst 1.0
  pow 1 x = x
  pow (suc n) dx = dx * pow n dx

  log e^_ recip abs sgn : ∀ {k} → D ℝ-mod ℝ-mod k → D ℝ-mod ℝ-mod k
  log = ℝ.log >-< recip ∘ abs

  recip (z x) = z (1.0 ℝ.÷ x)
  recip dfx@(d fx f'x) = d (1.0 ℝ.÷ fx) λ x → - (f'x x * tmp * tmp)
    where
      tmp = recip (hack dfx)

  abs = ℝ-abs >-< sgn

  sgn = ℝ-sgn >-< λ _ → 0ᴹ

  e^ z x = z (ℝ.e^ x)
  e^ dfx@(d fx f'x) = d (run tmp) λ v → f'x v * tmp
    where
      tmp = e^ hack dfx

  infixl 7 _÷_
  _÷_ _**_ : ∀ {k} (x y : D ℝ-mod ℝ-mod k) → D ℝ-mod ℝ-mod k
  x ÷ y = x * recip x
  x ** y = e^ y * log x


  _! : ℕ → ℕ
  0 ! = 1
  1 ! = 1
  sucn@(suc n) ! = sucn ℕ.* (n !)


  sterling : ∀ {k} → ℕ → D ℝ-mod ℝ-mod k
  sterling {k} m = m' * log m' - m'
    where
      m' : D ℝ-mod ℝ-mod k
      m' = ℝ.fromℕ m #


  -- without the constant denominator term
  logPoisson' : ∀ {n} → ℕ → D ℝ-mod ℝ-mod n → D ℝ-mod ℝ-mod n
  logPoisson' k λ' = k' * log λ' - λ'
    where k' = ℝ.fromℕ k #

  logPoisson : ∀ {n} → ℕ → D ℝ-mod ℝ-mod n → D ℝ-mod ℝ-mod n
  logPoisson k λ' = logPoisson' k λ' - sterling k


  -- descend : ∀ {rank} (f : D (ℝ^ rank) 1 → D ℝ-mod 1) (steps : ℕ) (start : ℝ ^ rank) → ℝ ^ rank
  -- descend f zero start = start
  -- descend f (suc steps) start = {!   !}


  module _ where
    open import Relation.Binary.PropositionalEquality using (refl)

    _ : (∇ (var 1.0 * var 1.0)) ℝ.≈ 2.0
    _ = refl

-- -- --   _ : run e^_ 2.0 ℝ.≈ (ℝ.e^ 2.0)
-- -- --   _ = refl


-- -- --   testpoly : ∀ {n} → D ℝ-mod n → D ℝ-mod n
-- -- --   testpoly = poly (1.0 , 2.0 , 3.0)


-- -- --   _ : run testpoly 2.0 ℝ.≈ (1.0 + 4.0 + 12.0)
-- -- --   _ = refl

-- -- --   _ : ∇ testpoly [ 2.0 ] ℝ.≈ (0.0 + 2.0 + 3.0 ℝ.* 2.0 ℝ.* 2.0)
-- -- --   _ = refl

-- -- --   _ : ∇ testpoly [ 7.0 ] ℝ.≈ (0.0 + 2.0 + 2.0 ℝ.* 3.0 ℝ.* 7.0)
-- -- --   _ = refl

-- -- --   _ : hessian e^_ 1.0 1.0 0.0 ℝ.≈ (ℝ.e^ 1.0)
-- -- --   _ = refl

-- -- --   asdf : D ℝ-mod 2
-- -- --   asdf = e^ var (2.0 , 1.0 , 0.0)

-- -- --   _ : hessian (poly (1.0 , 2.0 , 3.0)) 1.0 1.0 0.0 ℝ.≈ (2.0 ℝ.* 3.0)
-- -- --   _ = refl

-- -- --   _ : ∇ log [ 1.0 ] ℝ.≈ 1.0
-- -- --   _ = refl

-- -- --   _ : ∇ log [ -ᴹ 1.0 ] ℝ.≈ 1.0
-- -- --   _ = refl

-- -- --   _ : ∇ sgn [ 2.0 ] ℝ.≈ 0.0
-- -- --   _ = refl

-- -- --   _ : ∇ abs [ 2.0 ] ℝ.≈ 1.0
-- -- --   _ = refl

-- -- --   _ : run abs (- 2.0) ℝ.≈ 2.0
-- -- --   _ = refl

-- -- --   _ : ∇ abs [ - 1.0 ] ℝ.≈ (- 1.0)
-- -- --   _ = refl

-- -- --   _ : ∇ recip [ - 2.0 ] ℝ.≈ (- 0.25)
-- -- --   _ = refl

-- -- --   _ : ∇ log [ 2.0 ] ℝ.≈ 0.5
-- -- --   _ = refl