{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.ActionFormulas where

open import Common.Biconditional using (_⇔_)
open import Common.RegularFormulasWithData using (ActionFormula; _∈_)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.Auxiliary using (∈-dec)
open import Relation.Nullary using (no; yes)

open ActionFormula

private variable
  a ℓ : Level
  α : Set a

|α₁∪α₂|ᶜ⇔|α₁ᶜ|∩|α₂ᶜ| : (a : α) → (af₁ af₂ : ActionFormula α ℓ) → a ∈ (af₁ ∪ af₂) ᶜ ⇔ a ∈ (af₁ ᶜ) ∩ (af₂ ᶜ)
|α₁∪α₂|ᶜ⇔|α₁ᶜ|∩|α₂ᶜ| a af₁ af₂ = |α₁∪α₂|ᶜ→|α₁ᶜ|∩|α₂ᶜ| a af₁ af₂ , |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ a af₁ af₂
  where
  |α₁∪α₂|ᶜ→|α₁ᶜ|∩|α₂ᶜ| : (a : α) → (af₁ af₂ : ActionFormula α ℓ) → a ∈ (af₁ ∪ af₂) ᶜ → a ∈ (af₁ ᶜ) ∩ (af₂ ᶜ)
  |α₁∪α₂|ᶜ→|α₁ᶜ|∩|α₂ᶜ| a af₁ af₂ h with ∈-dec a af₁
  ... | yes h₁ = ⊥₀-elim (h (inj₁ h₁))
  ... | no hn₁ with ∈-dec a af₂
  ...   | no hn₂ = hn₁ , hn₂
  ...   | yes h₂ = ⊥₀-elim (h (inj₂ h₂))

  |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ : (a : α) → (af₁ af₂ : ActionFormula α ℓ) → a ∈ (af₁ ᶜ) ∩ (af₂ ᶜ) → a ∈ (af₁ ∪ af₂) ᶜ
  |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ _ _ _ (hn₁ , _) (inj₁ h₁) = hn₁ h₁
  |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ _ _ _ (_ , hn₂) (inj₂ h₂) = hn₂ h₂

|α₁∩α₂|ᶜ⇔|α₁ᶜ|∪|α₂ᶜ| : (a : α) → (af₁ af₂ : ActionFormula α ℓ) → a ∈ (af₁ ∩ af₂) ᶜ ⇔ a ∈ (af₁ ᶜ) ∪ (af₂ ᶜ)
|α₁∩α₂|ᶜ⇔|α₁ᶜ|∪|α₂ᶜ| a af₁ af₂ = |α₁∩α₂|ᶜ→|α₁ᶜ|∪|α₂ᶜ| a af₁ af₂ , |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ a af₁ af₂
  where
  |α₁∩α₂|ᶜ→|α₁ᶜ|∪|α₂ᶜ| : (a : α) → (af₁ af₂ : ActionFormula α ℓ) → a ∈ (af₁ ∩ af₂) ᶜ → a ∈ (af₁ ᶜ) ∪ (af₂ ᶜ)
  |α₁∩α₂|ᶜ→|α₁ᶜ|∪|α₂ᶜ| a af₁ af₂ h with ∈-dec a af₁
  ... | no hn₁ = inj₁ hn₁
  ... | yes h₁ with ∈-dec a af₂
  ...   | no hn₂ = inj₂ hn₂
  ...   | yes h₂ = ⊥₀-elim (h (h₁ , h₂))

  |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ : (a : α) → (af₁ af₂ : ActionFormula α ℓ) → a ∈ (af₁ ᶜ) ∪ (af₂ ᶜ) → a ∈ (af₁ ∩ af₂) ᶜ
  |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ _ _ _ (inj₁ hn₁) (h₁ , _) = hn₁ h₁
  |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ _ _ _ (inj₂ hn₂) (_ , h₂) = hn₂ h₂

|∀d:D．A|d||ᶜ⇔∃d:D．|A|d||ᶜ : (a : α) → (D : Set ℓ) → (af : D → ActionFormula α ℓ) → a ∈ (∀⦗ D ⦘ λ d → af d) ᶜ ⇔ a ∈ ∃⦗ D ⦘ λ d → (af d) ᶜ
|∀d:D．A|d||ᶜ⇔∃d:D．|A|d||ᶜ a D af = |∀d:D．A|d||ᶜ→∃d:D．|A|d||ᶜ a D af , ∃d:D．|A|d||ᶜ→|∀d:D．A|d||ᶜ a D af
  where
  |∀d:D．A|d||ᶜ→∃d:D．|A|d||ᶜ : (a : α) → (D : Set ℓ) → (af : D → ActionFormula α ℓ) → a ∈ (∀⦗ D ⦘ λ d → af d) ᶜ → a ∈ ∃⦗ D ⦘ λ d → (af d) ᶜ
  |∀d:D．A|d||ᶜ→∃d:D．|A|d||ᶜ a D af hn∀ with ∈-dec a (∃⦗ D ⦘ λ d → (af d) ᶜ)
  ... | no hn∃ = ⊥₀-elim (hn∀ λ d → case ∈-dec a (af d) of λ { (no hn) → ⊥₀-elim (hn∃ (d , hn))
                                                             ; (yes h) → h })
  ... | yes h∃ = h∃

  ∃d:D．|A|d||ᶜ→|∀d:D．A|d||ᶜ : (a : α) → (D : Set ℓ) → (af : D → ActionFormula α ℓ) → a ∈ ∃⦗ D ⦘ (λ d → (af d) ᶜ) → a ∈ (∀⦗ D ⦘ λ d → af d) ᶜ
  ∃d:D．|A|d||ᶜ→|∀d:D．A|d||ᶜ _ _ _ (d , hn) h = hn (h d)
