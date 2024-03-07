{-# OPTIONS --without-K --safe #-}
module Common.Utils where

open import Level using (Level; _⊔_)

private variable
  ℓ₁ ℓ₂ : Level

infix 20 _⇔_

record _⇔_ (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
      to : α → β
      from : β → α
