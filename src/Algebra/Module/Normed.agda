module Algebra.Module.Normed where

open import Assume using (assume)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Bundles using (Module)
open import Level using (_⊔_; suc)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Rel)
open import Function.Metric using (IsGeneralMetric)

module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  {m ℓm} (M : Module CR m ℓm)
  where
  
  private
    module CR = CommutativeRing CR
    module M = Module M

  module _
    {rel} (_≤_ : Rel CR.Carrier rel)
    (∥_∥ : M.Carrierᴹ → CR.Carrier)
    where

    record IsNormedModule : Set (r ⊔ ℓr ⊔ m ⊔ ℓm ⊔ rel) where
      open CommutativeRing CR public
      open M public

      field
        triangle-norm : ∀ x y → (∥ x +ᴹ y ∥) ≤ (∥ x ∥ + ∥ y ∥)
        homogeneity : ∀ s x → ∥ s *ₗ x ∥ ≈ s * ∥ x ∥
        positive-definite : ∀ x → ∥ x ∥ ≈ 0# → x ≈ᴹ 0ᴹ

      infixl 6 _-ᴹ_
      _-ᴹ_ : Carrierᴹ → Carrierᴹ → Carrierᴹ
      x -ᴹ y = x +ᴹ (-ᴹ y)

      ⟨_,_⟩ : Carrierᴹ → Carrierᴹ → Carrier
      ⟨ x , y ⟩ = ∥ x -ᴹ y ∥

      isGeneralMetric : IsGeneralMetric _≈ᴹ_ _≈_ _≤_ 0# _+_ ⟨_,_⟩
      isGeneralMetric = assume

      open IsGeneralMetric isGeneralMetric public hiding (refl; reflexive)


module _
  {r ℓr} (CR : CommutativeRing r ℓr)
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} (_≤_ : Rel X rel)
  m ℓm
  where

  record NormedModule : Set (suc (r ⊔ ℓr ⊔ m ⊔ ℓm ⊔ rel)) where
    module CR = CommutativeRing CR
    field
      M : Module CR m ℓm

    module M = Module M

    field
      ∥_∥ : M.Carrierᴹ → CR.Carrier
      isNormedModule : IsNormedModule M _≤_ ∥_∥

    open IsNormedModule isNormedModule public


module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  {ma ℓma} (MA : NormedModule CR _≤_ ma ℓma)
  {mb ℓmb} (MB : NormedModule CR _≤_ mb ℓmb)
  where

  private
    module CR = CommutativeRing CR
    module MA = NormedModule MA
    module MB = NormedModule MB

  directProduct : NormedModule CR _≤_ (ma ⊔ mb) (ℓma ⊔ ℓmb)
  directProduct =
    record
    { M = ⟨module⟩ MA.M MB.M
    ; ∥_∥ = (uncurry CR._+_) ∘ (map MA.∥_∥ MB.∥_∥)
    ; isNormedModule = assume
    }
    where
      open import Algebra.Module.Construct.DirectProduct
      open import Function using (_∘_)
      open import Data.Product using (uncurry; map)


module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  (∥_∥ : X → X)
  where

  tensorUnit : NormedModule CR _≤_ r ℓr
  tensorUnit =
    record
    { M = ⟨module⟩
    ; ∥_∥ = ∥_∥
    ; isNormedModule = assume
    }
    where open import Algebra.Module.Construct.TensorUnit


module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  where

  null : ∀ {c l} → NormedModule CR _≤_ c l
  null =
    record
    { M = ⟨module⟩
    ; ∥_∥ = λ _ → 0#
    ; isNormedModule = assume
    }
    where
      open import Algebra.Module.Construct.Zero
      open CommutativeRing CR


-- TODO
-- →NormedModule