open import Algebra.Bundles using (CommutativeRing)

module Algebra.Module.Diff 
  {r ℓr} {CR : CommutativeRing r ℓr}
  where

open import Assume using (assume)
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)

open import Relation.Binary using (Rel)

open import Algebra.Module using (Module)
open Module

open import Function using (_∘_)
open import Data.Product using (proj₁; proj₂; _,_)

open import Algebra.Module.Morphism.Module using (→-module'; →-module; ⊸-module; _⊸_)
open import Algebra.Module.Construct.DirectProduct using () renaming (⟨module⟩ to ×-module)
open import Level using (_⊔_; Level)


private
  variable
    ma mℓa mb mℓb mc mℓc : Level

D-module : (MA : Module CR ma mℓa) (MB : Module CR mb mℓb) → Module CR _ _
D-module MA MB = →-module' MA (×-module MB (⊸-module MA MB))

instance
  D-module' : {MA : Module CR ma mℓa} {MB : Module CR mb mℓb} → Module CR _ _
  D-module' {MA = MA} {MB = MB} = →-module' MA (×-module MB (⊸-module MA MB))

D : (MA : Module CR ma mℓa) (MB : Module CR mb mℓb) → Set (r ⊔ ma ⊔ mℓa ⊔ mb ⊔ mℓb)
D MA MB = Carrierᴹ (→-module' MA (×-module MB (⊸-module MA MB)))

compose
  : {MA : Module CR ma mℓa} {MB : Module CR mb mℓb} {MC : Module CR mc mℓc}
  → D MB MC → D MA MB → D MA MC
compose {MA = MA} {MB = MB} {MC = MC} dbc dab a =
  let (b , a⊸b) = dab a
      (c , b⊸c) = dbc b
  in c , ⊸-compose b⊸c a⊸b
  where
    ⊸-compose : MB ⊸ MC → MA ⊸ MB → MA ⊸ MC
    ⊸-compose (b→c , b→c-ishom) (a→b , a→b-ishom) = b→c ∘ a→b , assume


run
  : ∀ {ma mℓa mb mℓb} {MA : Module CR ma mℓa} {MB : Module CR mb mℓb}
  → D MA MB → Carrierᴹ MA → Carrierᴹ MB
run f = proj₁ ∘ f

∇_[_]∙_
  : ∀ {ma mℓa mb mℓb} {MA : Module CR ma mℓa} {MB : Module CR mb mℓb}
  → D MA MB → Carrierᴹ MA → Carrierᴹ MA → Carrierᴹ MB
∇_[_]∙_ f = proj₁ ∘ proj₂ ∘ f

grad
  : ∀ {ma mℓa mb mℓb} {MA : Module CR ma mℓa} {MB : Module CR mb mℓb}
  → D MA MB → Carrierᴹ MA → Carrierᴹ MA → Carrierᴹ MB
grad f = proj₁ ∘ proj₂ ∘ f

