{-# OPTIONS --without-K --safe #-}
module Common.Utils where

open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Product using (_,_; ∃-syntax)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no)

open _⋆_
open IsDecEquivalence ⦃...⦄

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 20 _⇔_

record _⇔_ (α : Set ℓ₁) (β : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
      to : α → β
      from : β → α

data Maybe' (α : Set ℓ) : Set ℓ where
  val : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

infix 30 ⟪_⟫_
infix 30 ⟦_⟧_

data ModalitySequence (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  ⟪_⟫_ : Shape C → ModalitySequence C → ModalitySequence C
  ⟦_⟧_ : Shape C → ModalitySequence C → ModalitySequence C
  ε : ModalitySequence C

unfold : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → ModalitySequence C → C ⋆ α → (Maybe' (C ⋆ α) → Set (ℓ₂ ⊔ ℓ₄)) → Set (ℓ₂ ⊔ ℓ₄)
unfold (⟪ _ ⟫ _) (pure _) f = f fail
unfold {ℓ₄ = ℓ} (⟪ s₁ ⟫ m) (impure (s₂ , c)) f with s₁ ≟ s₂
... | no _ = f fail
... | yes _ = ∃[ p ] unfold {ℓ₄ = ℓ} m (c p) f
unfold (⟦ _ ⟧ _) (pure _) f = f done
unfold {ℓ₄ = ℓ} (⟦ s₁ ⟧ m) (impure (s₂ , c)) f with s₁ ≟ s₂
... | no _ = f done
... | yes _ = ∀ p → unfold {ℓ₄ = ℓ} m (c p) f
unfold ε x f = f (val x)
