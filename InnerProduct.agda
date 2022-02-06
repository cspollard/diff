{-# OPTIONS --allow-unsolved-metas #-}

module InnerProduct where

open import Algebra.Bundles using (CommutativeRing)
open import NormedModule using (NormedModule)
open import Level using (_⊔_; suc)
open import Relation.Nullary using (¬_)


module _
  {r ℓr} (CR : CommutativeRing r ℓr)
  m ℓm rel
  where

module _
  {r ℓr} {CR : CommutativeRing r ℓr}
  (open CommutativeRing CR renaming (Carrier to S))
  {rel} {_<_ : S → S → Set rel} (STO : IsStrictTotalOrder _≈_ _<_)
  (_† : S → S) 
  {m ℓm} (M : Module CR m ℓm)
  (open Module M renaming (Carrierᴹ to A))
  (⟨_,_⟩ : A → A → S)
  where

  record IsInnerProduct : Set (r ⊔ ℓr ⊔ suc (m ⊔ ℓm ⊔ rel)) where
    field
      ⟨,⟩-linear-+ : ∀ x y z → ⟨ x +ᴹ y , z ⟩ ≈ ⟨ x , z ⟩ + ⟨ y , z ⟩
      ⟨,⟩-linear-* : ∀ s x y → ⟨ s *ₗ x , y ⟩ ≈ s * ⟨ x , y ⟩
      ⟨,⟩-cong : ∀ {x y} → x ≈ᴹ y → ⟨ x , x ⟩ ≈ ⟨ y , y ⟩
      †-linear-+ : ∀ x y → (x + y) † ≈ x † + y †
      †-cong : ∀ {s t} → s ≈ t → s † ≈ t †
      †-inv : ∀ s → (s †) † ≈ s
      ⟨,⟩-herm : ∀ x y → ⟨ x , y ⟩ ≈ ⟨ y , x ⟩ †

    real : S → Set _
    real s = s ≈ s †

    field
      ⟨x,x⟩-real : ∀ x → real ⟨ x , x ⟩
      positive-definite : ∀ {x} → ¬ (x ≈ᴹ 0ᴹ) → 0# < ⟨ x , x ⟩

    open IsStrictTotalOrder STO public
    open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_ public using (_≤_)


    _-ᴹ_ : A → A → A
    x -ᴹ y = x +ᴹ (-ᴹ y)

    ∥_∥² : A → S
    ∥ x ∥² = ⟨ x , x ⟩

    -- TODO
    -- is this universally true?
    -- or just common?
    ∥-x∥²≈∥x∥² : ∀ x → ∥ -ᴹ x ∥² ≈ ∥ x ∥²
    ∥-x∥²≈∥x∥² = {!   !}

    -- ∥a-b∥≤∥a∥-∥b∥ : ∀ a b → ∥ a -ᴹ b ∥² ≤ ∥ a ∥² - ∥ b ∥²
    -- ∥a-b∥≤∥a∥-∥b∥ = {!   !}

    
    [s+s†]†≈s+s† : ∀ s → (s + s †) † ≈ s + s †
    [s+s†]†≈s+s† s =
      begin
        (s + s †) †
      ≈⟨ †-linear-+ s (s †) ⟩
        (s † + (s †) †) 
      ≈⟨ +-cong refl (†-inv _) ⟩
        (s † + s) 
      ≈⟨ +-comm _ _ ⟩
        (s + s †)
      ∎
      where open import Relation.Binary.Reasoning.Setoid setoid


