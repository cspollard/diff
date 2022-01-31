module Algebra.Module.Morphism.Module where

open import Assume using (assume)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Bundles using (Module)
open import Algebra.Module.Structures using (IsModule)
open import Algebra.Module.Normed using (IsNormedModule; NormedModule)
open import Relation.Binary.Core using (Rel)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁)

open import Algebra.Module.Morphism.Structures
  using (IsModuleHomomorphism; IsModuleMonomorphism; IsModuleIsomorphism)

open import Level using (_⊔_; suc)

private
  module toModule
    {a} (A : Set a)
    {r ℓr} {CR : CommutativeRing r ℓr}
    {mb ℓmb} (MB : Module CR mb ℓmb)
    where

    private
      module CR = CommutativeRing CR
      module MB = Module MB

      Carrierᴹ : Set _
      Carrierᴹ = A → MB.Carrierᴹ

      _≈ᴹ_ : Rel Carrierᴹ _
      f ≈ᴹ g = ∀ a → f a MB.≈ᴹ g a

      _+ᴹ_ : Op₂ Carrierᴹ
      f +ᴹ g = λ a → f a MB.+ᴹ g a

      _*ₗ_ : CR.Carrier → Carrierᴹ → Carrierᴹ
      s *ₗ f = λ a → s MB.*ₗ f a

      _*ᵣ_ : Carrierᴹ → CR.Carrier → Carrierᴹ
      f *ᵣ s = λ a → f a MB.*ᵣ s

      0ᴹ : Carrierᴹ
      0ᴹ _ = MB.0ᴹ

      -ᴹ_ : Op₁ Carrierᴹ
      -ᴹ_ f = λ a → MB.-ᴹ f a

    isModule : IsModule CR _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_ 
    isModule = assume


→-module
  : ∀ {a} (A : Set a)
    {r ℓr} {CR : CommutativeRing r ℓr}
    {mb ℓmb} (MB : Module CR mb ℓmb)
  → Module CR (a ⊔ mb) (a ⊔ ℓmb)
→-module A MB = record { toModule A MB }

module _ 
  {r ℓr} {CR : CommutativeRing r ℓr}
  {ma ℓma} (MA : Module CR ma ℓma)
  {mb ℓmb} (MB : Module CR mb ℓmb)
  where

  private
    module MA = Module MA
    module MB = Module MB

  _⊸_ : Set _
  _⊸_ = ∃[ f ] IsModuleHomomorphism MA MB f

  ⊸-module : Module CR (r ⊔ ma ⊔ ℓma ⊔ mb ⊔ ℓmb) (ma ⊔ ℓmb)
  ⊸-module =
    record
    { Carrierᴹ = _⊸_
    ; _≈ᴹ_ = λ f g → ∀ x → proj₁ f x MB.≈ᴹ proj₁ g x
    ; _+ᴹ_ = λ f g → (λ x → proj₁ f x MB.+ᴹ proj₁ g x) , assume
    ; _*ₗ_ = λ s f → (λ x → s MB.*ₗ proj₁ f x) , assume
    ; _*ᵣ_ = λ f s → (λ x → proj₁ f x MB.*ᵣ s) , assume
    ; 0ᴹ = (λ x → MB.0ᴹ) , assume
    ; -ᴹ_ = λ f → (λ x → MB.-ᴹ proj₁ f x) , assume
    ; isModule = assume
    }

module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to S))
  {rel} {_≤_ : Rel S rel}
  {ma ℓma} (MA : NormedModule CR _≤_ ma ℓma)
  {mb ℓmb} (MB : NormedModule CR _≤_ mb ℓmb)
  where

  private
    module MB = NormedModule MB
    module MA = NormedModule MA

  ⊸-normed : NormedModule CR _≤_ _ _
  ⊸-normed =
    record
    { M = ⊸-module MA.M MB.M
    ; ∥_∥ = λ f → MB.∥ proj₁ f MA.0ᴹ ∥
    ; isNormedModule = assume
    }

