{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.PredicateLogic where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program)
open import Data.Bool using (Bool)
open import Data.Container using (Container; Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.List using (List)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Context; Formulaⁱ; _⊢_⊨'_; _⊢_⊨ⁱ_)
open import ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.Auxiliary using (⊨ⁱ-dec)
open import Relation.Nullary using (no; yes)

open Formulaⁱ
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

-- Theorems for ∀⦗_⦘_

∀d:D．|Φ|d|∨ψ|⇔|∀d:D．Φ|d||∨ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ : D → Formulaⁱ (Shape C) ℓ prev flags) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ₁ d ∨ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ (∀⦗ D ⦘ λ d → fⁱ₁ d) ∨ fⁱ₂
∀d:D．|Φ|d|∨ψ|⇔|∀d:D．Φ|d||∨ψ Γ x D fⁱ₁ fⁱ₂ = ∀d:D．|Φ|d|∨ψ|→|∀d:D．Φ|d||∨ψ Γ x D fⁱ₁ fⁱ₂ , |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| Γ x D fⁱ₁ fⁱ₂
  where
  ∀d:D．|Φ|d|∨ψ|→|∀d:D．Φ|d||∨ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ : D → Formulaⁱ (Shape C) ℓ prev flags) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ₁ d ∨ fⁱ₂) → Γ ⊢ x ⊨ⁱ (∀⦗ D ⦘ λ d → fⁱ₁ d) ∨ fⁱ₂
  ∀d:D．|Φ|d|∨ψ|→|∀d:D．Φ|d||∨ψ Γ x _ _ fⁱ₂ (`∀ h) with ⊨ⁱ-dec Γ x fⁱ₂
  ... | no hn₂ = inj₁ (`∀ λ d → case h d of λ { (inj₁ h₁) → h₁
                                              ; (inj₂ h₂) → ⊥₀-elim (hn₂ h₂) })
  ... | yes h₂ = inj₂ h₂

  |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ : D → Formulaⁱ (Shape C) ℓ prev flags) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (∀⦗ D ⦘ λ d → fⁱ₁ d) ∨ fⁱ₂ → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ₁ d ∨ fⁱ₂)
  |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| _ _ _ _ _ (inj₁ (`∀ h₁)) = `∀ λ d → inj₁ (h₁ d)
  |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| _ _ _ _ _ (inj₂ h₂) = `∀ λ _ → inj₂ h₂
