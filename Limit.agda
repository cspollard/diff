open import Relation.Binary using (Rel)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Morphism.Structures
open import Normed using (NormedModule)


module Limit
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR using () renaming (Carrier to X))
  {rel} {_≤_ : Rel X rel}
  {ma ℓma} (MA : NormedModule CR _≤_ ma ℓma)
  {mb ℓmb} (MB : NormedModule CR _≤_ mb ℓmb)
  where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_)

open CommutativeRing CR
private 
  module MA = NormedModule MA
  module MB = NormedModule MB

open NormedModule MA using () renaming
  ( Carrierᴹ to Carrierᴬ
  ; _+ᴹ_ to _+ᴬ_
  ; _-ᴹ_ to _-ᴬ_
  ; ∥_∥ to ∥_∥ᴬ
  ; ⟨_,_⟩ to ⟨_,_⟩ᴬ
  )

open NormedModule MB using () renaming
  ( Carrierᴹ to Carrierᴮ
  ; _+ᴹ_ to _+ᴮ_
  ; _-ᴹ_ to _-ᴮ_
  ; ∥_∥ to ∥_∥ᴮ
  ; ⟨_,_⟩ to ⟨_,_⟩ᴮ
  )

open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_ using (_<_)

Limit-syntax : (L : Carrierᴮ) (f : Carrierᴬ → Carrierᴮ) (c : Carrierᴬ) → Set _
Limit-syntax L f c =
  ∀ ε → 0# < ε → ∃[ δ ]
    ∀ x →
      let d = ⟨ c , x ⟩ᴬ
      in (0# < d) × (d < δ) → ∥ f x -ᴮ L ∥ᴮ < ε

syntax Limit-syntax L (λ x → f) c = f ⟶ L As x ⟶ c

Limit-syntax-0 : (L : Carrierᴮ) (f : Carrierᴬ → Carrierᴮ) → Set _
Limit-syntax-0 L f =
  ∀ ε → 0# < ε → ∃[ δ ]
    ∀ x →
      let d = ∥ x ∥ᴬ
      in (0# < d) × (d < δ) → ∥ f x -ᴮ L ∥ᴮ < ε

syntax Limit-syntax-0 L (λ x → f) = f ⟶ L As x ⟶0

Limit-syntax-0-0 : (f : Carrierᴬ → Carrierᴮ) → Set _
Limit-syntax-0-0 f =
  ∀ ε → 0# < ε → ∃[ δ ]
    ∀ x →
      let d = ∥ x ∥ᴬ
      in (0# < d) × (d < δ) → ∥ f x ∥ᴮ < ε

syntax Limit-syntax-0-0 (λ x → f) = f ⟶0 As x ⟶0

_Approximates_At_
  : (δf : Carrierᴬ → Carrierᴬ → Carrierᴮ)
  → (f : Carrierᴬ → Carrierᴮ)
  → (x : Carrierᴬ)
  → Set _
δf Approximates f At x = (f (x +ᴬ dx) -ᴮ (f x +ᴮ δf x dx)) ⟶0 As dx ⟶0

_Differentiates_At_
  : (Carrierᴬ → Carrierᴬ → Carrierᴮ)
  → (Carrierᴬ → Carrierᴮ)
  → Carrierᴬ
  → Set _
δf Differentiates f At x = IsModuleHomomorphism MA.M MB.M (δf x) × (δf Approximates f At x)

_DifferentiableAt_ : (f : Carrierᴬ → Carrierᴮ) (x : Carrierᴬ) → Set _
f DifferentiableAt x = Σ[ δf ∈ (Carrierᴬ → Carrierᴬ → Carrierᴮ) ] δf Differentiates f At x

Differentiable : (f : Carrierᴬ → Carrierᴮ) → Set _
Differentiable f = ∀ x → f DifferentiableAt x

D[_,_][_,_] : (f : Carrierᴬ → Carrierᴮ) (x : Carrierᴬ) → Set _
D[_,_][_,_] f x = f DifferentiableAt x
