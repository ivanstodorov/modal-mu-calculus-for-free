{-# OPTIONS --without-K --safe #-}
module Common.Container where

open import Data.Bool using (false)
open import Data.Container using (Container)
open import Data.Sum using (_⊎_)
open import Function using (_∘_; id)
open import Level using (Level; _⊔_; Lift; lift)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (isDecEquivalence)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ; _because_)

open Container
open _⊎_
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

_:+:_ : Container ℓ₁ ℓ₂ → Container ℓ₃ ℓ₄ → Container (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄)
Shape (C₁ :+: C₂) = Shape C₁ ⊎ Shape C₂
Position (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} C₁ C₂) (inj₁ s) = Lift (ℓ₂ ⊔ ℓ₄) (Position C₁ s)
Position (_:+:_ {ℓ₂ = ℓ₂} {ℓ₄ = ℓ₄} C₁ C₂) (inj₂ s) = Lift (ℓ₂ ⊔ ℓ₄) (Position C₂ s)

instance
  effectSumEqIsDecEq : {C₁ : Container ℓ₁ ℓ₂} → {C₂ : Container ℓ₃ ℓ₄} → ⦃ IsDecEquivalence {A = Shape C₁} _≡_ ⦄ → ⦃ IsDecEquivalence {A = Shape C₂} _≡_ ⦄ → IsDecEquivalence {A = Shape (C₁ :+: C₂)} _≡_
  effectSumEqIsDecEq {C₁ = C₁} {C₂ = C₂} = isDecEquivalence effectSumEqDec
    where
    effectSumEqDec : Decidable {A = Shape (C₁ :+: C₂)} _≡_
    does (effectSumEqDec (inj₁ s₁) (inj₁ s₂)) with s₁ ≟ s₂
    ... | h because _ = h
    does (effectSumEqDec (inj₁ _) (inj₂ _)) = false
    does (effectSumEqDec (inj₂ _) (inj₁ _)) = false
    does (effectSumEqDec (inj₂ s₁) (inj₂ s₂)) with s₁ ≟ s₂
    ... | h because _ = h
    proof (effectSumEqDec (inj₁ s₁) (inj₁ s₂)) with s₁ ≟ s₂
    ... | yes refl = ofʸ refl
    ... | no ¬p = ofⁿ λ { refl → ¬p refl }
    proof (effectSumEqDec (inj₁ _) (inj₂ _)) = ofⁿ λ ()
    proof (effectSumEqDec (inj₂ _) (inj₁ _)) = ofⁿ λ ()
    proof (effectSumEqDec (inj₂ s₁) (inj₂ s₂)) with s₁ ≟ s₂
    ... | yes refl = ofʸ refl
    ... | no ¬p = ofⁿ λ { refl → ¬p refl }

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

  C₁:<:|C₁:+:C₂| : {C₁ : Container ℓ₁ ℓ₂} → {C₂ : Container ℓ₃ ℓ₄} → C₁ :<: (C₁ :+: C₂)
  injS ⦃ C₁:<:|C₁:+:C₂| ⦄ = inj₁
  projP ⦃ C₁:<:|C₁:+:C₂| ⦄ (lift p) = p

  C₁:<:C₂→C₁:<:|C₃:+:C₂| : {C₁ : Container ℓ₁ ℓ₂} → {C₂ : Container ℓ₃ ℓ₄} → {C₃ : Container ℓ₅ ℓ₆} → ⦃ C₁ :<: C₂ ⦄ → C₁ :<: (C₃ :+: C₂)
  injS ⦃ C₁:<:C₂→C₁:<:|C₃:+:C₂| ⦃ inst ⦄ ⦄ = inj₂ ∘ injS inst
  projP ⦃ C₁:<:C₂→C₁:<:|C₃:+:C₂| ⦃ inst ⦄ ⦄ (lift p) = projP inst p
