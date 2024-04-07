{-# OPTIONS --without-K --safe #-}
module Common.Container where

open import Data.Bool using (true; false)
open import Data.Container using (Container; _▷_)
open import Data.Container.Combinator using (_⊎_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; case_of_; id)
open import Level using (Level; _⊔_; Lift)
open import Relation.Binary.PropositionalEquality using (_≡_; isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no; ofʸ; ofⁿ)

open Container
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl)

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

_⊎'_ : Container ℓ₁ ℓ₂ → Container ℓ₃ ℓ₄ → Container (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
_⊎'_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} (S₁ ▷ P₁) (S₂ ▷ P₂) = S₁ ▷ Lift (ℓ₂ ⊔ ℓ₄) ∘ P₁ ⊎ S₂ ▷ Lift (ℓ₂ ⊔ ℓ₄) ∘ P₂

-- instance
--   effectSum-decEq : {C₁ : Container ℓ₁ ℓ₂} → {C₂ : Container ℓ₃ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C₁} _≡_ ⦄ → ⦃ IsDecEquivalence {A = Shape C₂} _≡_ ⦄ → IsDecEquivalence {A = Shape (C₁ ⊎ C₂)} _≡_
--   effectSum-decEq = isDecEquivalence λ { (inj₁ x) (inj₁ y) → case x ≟ y of λ { (no h) → record { does = false ; proof = ofⁿ λ { refl → h refl } }
--                                                                              ; (yes refl) → record { does = true ; proof = ofʸ refl } }
--                                        ; (inj₁ _) (inj₂ _) → record { does = false ; proof = ofⁿ λ () }
--                                        ; (inj₂ _) (inj₁ _) → record { does = false ; proof = ofⁿ λ () }
--                                        ; (inj₂ x) (inj₂ y) → case x ≟ y of λ { (no h) → record { does = false ; proof = ofⁿ λ { refl → h refl } }
--                                                                              ; (yes refl) → record { does = true ; proof = ofʸ refl } } }

record _:<:_ (C₁ : Container ℓ₁ ℓ₂) (C₂ : Container ℓ₃ ℓ₄) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    injS : Shape C₁ → Shape C₂
    projP : {s : Shape C₁} → Position C₂ (injS s) → Position C₁ s

open _:<:_
open _:<:_ ⦃...⦄

instance
  C:<:C : {C : Container ℓ₁ ℓ₂} → C :<: C
  injS ⦃ C:<:C ⦄ = id
  projP ⦃ C:<:C ⦄ = id

  C₁:<:|C₁⊎C₂| : {C₁ : Container ℓ₁ ℓ₂} → {C₂ : Container ℓ₃ ℓ₂} → C₁ :<: (C₁ ⊎ C₂)
  injS ⦃ C₁:<:|C₁⊎C₂| ⦄ = inj₁
  projP ⦃ C₁:<:|C₁⊎C₂| ⦄ = id

  C₁:<:C₂→C₁:<:|C₃⊎C₂| : {C₁ : Container ℓ₁ ℓ₂} → {C₂ : Container ℓ₃ ℓ₄} → {C₃ : Container ℓ₅ ℓ₄} → ⦃ C₁ :<: C₂ ⦄ → C₁ :<: (C₃ ⊎ C₂)
  injS ⦃ C₁:<:C₂→C₁:<:|C₃⊎C₂| ⦃ inst ⦄ ⦄ = inj₂ ∘ injS inst
  projP ⦃ C₁:<:C₂→C₁:<:|C₃⊎C₂| ⦃ inst ⦄ ⦄ = projP inst
