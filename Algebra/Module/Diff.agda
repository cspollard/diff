module Algebra.Module.Diff where

import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)

open import Algebra.Bundles using (CommutativeRing)
open import Relation.Binary using (Rel)
open import Algebra.Module.Normed using (NormedModule)
import Algebra.Module.Limit as Limit
open Limit using (D[_,_]_~_)


open import Function using (flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Level using (_⊔_; Level)
open import Assume using (assume)

module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  where

  open CommutativeRing CR
  open NormedModule using (Carrierᴹ) renaming (M to underlyingM)
  open import Algebra.Module.Morphism.Module

  data Diff
      {ma ℓma} (MA : NormedModule CR _≤_ ma ℓma)
      {mb ℓmb} (MB : NormedModule CR _≤_ mb ℓmb)
    : ℕ → Set (r ⊔ ℓr ⊔ rel ⊔ ma ⊔ ℓma ⊔ mb ⊔ ℓmb)

  func
    : ∀ {ma ℓma} {MA : NormedModule CR _≤_ ma ℓma}
      {mb ℓmb} {MB : NormedModule CR _≤_ mb ℓmb}
      {n}
    → Diff MA MB n
    → Carrierᴹ MA → Carrierᴹ MB

  data Diff MA MB where
      Dz : (f : Carrierᴹ MA → Carrierᴹ MB) → Diff MA MB ℕ.zero

      Ds
        : ∀ {n}
          (f : Carrierᴹ MA → Carrierᴹ MB)
          (diff-df : Diff MA (⊸-normed MA MB) n)
        → (D[ MA , MB ] f ~ func diff-df) 
        → Diff MA MB (suc n)

  func (Dz f) = f
  func (Ds f d x) = f


  module _ where
    open import Algebra.Module.Bundles using (Module)
    open import Algebra.Module.Normed using (NormedModule)



    private
      variable
        ma ℓma mb ℓmb : Level
        MA : NormedModule CR _≤_ ma ℓma
        MB : NormedModule CR _≤_ mb ℓmb



    _≈ᴹ_
      : ∀ {n : ℕ} {MA : NormedModule CR _≤_ ma ℓma} {MB : NormedModule CR _≤_ mb ℓmb}
        (x y : Diff MA MB n)
      → Set (ma ⊔ ℓmb)
    _≈ᴹ_ {MA = MA} {MB = MB} (Dz f) (Dz g) = f MAMB.≈ᴹ g
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))

    _≈ᴹ_ {MA = MA} {MB = MB} (Ds f df _) (Ds g dg _) = (f MAMB.≈ᴹ g) × (df ≈ᴹ dg)
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))


    _+ᴹ_ : ∀ {n : ℕ} (x y : Diff MA MB n) → Diff MA MB n
    _+ᴹ_ {MA = MA} {MB = MB} (Dz f) (Dz g) = Dz (f MAMB.+ᴹ g)
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))

    _+ᴹ_ {MA = MA} {MB = MB} (Ds f df _) (Ds g dg _)
      = Ds (f MAMB.+ᴹ g) (df +ᴹ dg) assume
        where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))


    _*ₗ_ : ∀ {n : ℕ} (s : Carrier) (d : Diff MA MB n) → Diff MA MB n
    _*ₗ_ {MA = MA} {MB = MB} s (Dz f) = Dz (s MAMB.*ₗ f)
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))

    _*ₗ_ {MA = MA} {MB = MB} s (Ds f d x) = Ds (s MAMB.*ₗ f) (s *ₗ d) assume
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))


    _*ᵣ_ : ∀ {n : ℕ} (d : Diff MA MB n) (s : Carrier) → Diff MA MB n
    _*ᵣ_ {MA = MA} {MB = MB} (Dz f) s = Dz (f MAMB.*ᵣ s)
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))

    _*ᵣ_ {MA = MA} {MB = MB} (Ds f d x) s = Ds (f MAMB.*ᵣ s) (d *ᵣ s) assume
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))


    0ᴹ : ∀ {n} → Diff MA MB n
    0ᴹ {MA = MA} {MB = MB} {zero} = Dz MAMB.0ᴹ
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))
    0ᴹ {MA = MA} {MB = MB} {suc n} = Ds MAMB.0ᴹ 0ᴹ assume
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))


    -ᴹ_ : ∀ {n} (d : Diff MA MB n) → Diff MA MB n 
    -ᴹ_ {MA = MA} {MB = MB} (Dz f) = Dz (MAMB.-ᴹ f)
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))
    -ᴹ_ {MA = MA} {MB = MB} (Ds f d _) = Ds (MAMB.-ᴹ f) (-ᴹ d) assume
      where module MAMB = Module (→-module (Carrierᴹ MA) (underlyingM MB))

module Iterated {r ℓr} {CR : CommutativeRing r ℓr} where

  open import Algebra.Module using (Module)
  open Module

  open import Algebra.Module.Morphism.Module
  open import Algebra.Module.Construct.DirectProduct as DP
  open import Algebra.Module.Construct.Zero as Z

  D^ : ∀ {ma ℓma mb ℓmb} (MA : Module CR ma ℓma) (MB : Module CR mb ℓmb) (n : ℕ)
    → Set (r ⊔ ma ⊔ ℓma ⊔ mb ⊔ ℓmb) 
  D^ {ma} {ℓma} {mb} {ℓmb} MA MB zero =
    Lift (r ⊔ ma ⊔ ℓma ⊔ mb ⊔ ℓmb) (Carrierᴹ MA → Carrierᴹ MB)
    where open import Level
  D^ MA MB (suc n) = D^ MA (⊸-module MA MB) n


  -- D^ 0 MA MB = A → B
  -- D^ 1 MA MB = A → (A ⊸ B)
  -- D^ 2 MA MB = A → (A ⊸ (A ⊸ B))

  -- D^ : ∀ {ma ℓma mb ℓmb} (MA : Module CR ma ℓma) (MB : Module CR mb ℓmb) (n : ℕ)
  --   → Module CR (r ⊔ ma ⊔ ℓma ⊔ mb ⊔ ℓmb) (ma ⊔ ℓmb)
  -- D^ MA MB zero = Z.⟨module⟩
  -- D^ MA MB (suc n) = (→-module (Carrierᴹ MA) (⊸-module MA (D^ MA MB n)))

  -- D : ∀ {ma ℓma mb ℓmb} (MA : Module CR ma ℓma) (MB : Module CR mb ℓmb) (n : ℕ)
  --   → Module CR (r ⊔ ma ⊔ ℓma ⊔ mb ⊔ ℓmb) (ma ⊔ ℓmb)
  -- D MA MB zero = Z.⟨module⟩
  -- D MA MB (suc n) = DP.⟨module⟩ (→-module (Carrierᴹ MA) (⊸-module MA MB)) (D MA (⊸-module MA MB) n)
  
