{-# OPTIONS --without-K --safe #-}
module Common.Injectable where

open import Data.Container using (Container)
open import Data.Container.Combinator using (_⊎_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; id)
open import Level using (Level; _⊔_)

open Container

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

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

inj : {C₁ : Container ℓ₁ ℓ₂} → Shape C₁ → (C₂ : Container ℓ₃ ℓ₄) → ⦃ C₁ :<: C₂ ⦄ → Shape C₂
inj s _ ⦃ inst ⦄ = injS inst s
