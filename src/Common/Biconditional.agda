{-# OPTIONS --without-K --safe #-}
module Common.Biconditional where

open import Data.Product using (_×_)
open import Level using (Level; _⊔_)

private variable
  ℓ₁ ℓ₂ : Level

_⇔_ : (α : Set ℓ₁) → (β : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
α ⇔ β = (α → β) × (β → α)
