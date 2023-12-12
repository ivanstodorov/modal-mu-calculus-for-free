module Common.Utils where

open import Level using (Level; _⊔_)

record _⇔_ {ℓ₁ ℓ₂ : Level} (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
      to : α → β
      from : β → α

infix 20 _⇔_
