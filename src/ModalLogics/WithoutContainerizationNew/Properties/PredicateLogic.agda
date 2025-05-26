{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.PredicateLogic where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container; Shape)
open import Data.List using (List; map)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Context; Formulaⁱ; _⊢_⊨'_; _⊢_⊨ⁱ_)
open import ModalLogics.WithoutContainerizationNew.Properties.Auxiliary using (Inhabited; defaultᶜ)

open Formulaⁱ
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

-- Theorems for ∀⦗_⦘_

∀d:D．φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ _ → fⁱ) ⇔ Γ ⊢ x ⊨ⁱ fⁱ
∀d:D．φ⇔φ Γ x D fⁱ = ∀d:D．φ→φ Γ x D fⁱ , φ→∀d:D．φ Γ x D fⁱ
  where
  ∀d:D．φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ _ → fⁱ) → Γ ⊢ x ⊨ⁱ fⁱ
  ∀d:D．φ→φ _ _ _ ⦃ defaultᶜ d ⦄ _ (`∀ h∀) = h∀ d

  φ→∀d:D．φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ _ → fⁱ)
  φ→∀d:D．φ _ _ _ _ h = `∀ λ _ → h

~∀d:D．Φ|d|⇔∃d:D．~Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (∀⦗ D ⦘ (λ d → fⁱ d)) ⇔ Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ λ d → ~ fⁱ d
~∀d:D．Φ|d|⇔∃d:D．~Φ|d| Γ x D fⁱ = ~∀d:D．Φ|d|→∃d:D．~Φ|d| Γ x D fⁱ , ∃d:D．~Φ|d|→~∀d:D．Φ|d| Γ x D fⁱ
  where
  ~∀d:D．Φ|d|→∃d:D．~Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (∀⦗ D ⦘ (λ d → fⁱ d)) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ λ d → ~ fⁱ d
  ~∀d:D．Φ|d|→∃d:D．~Φ|d| _ _ _ _ h = h

  ∃d:D．~Φ|d|→~∀d:D．Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → ~ fⁱ d) → Γ ⊢ x ⊨ⁱ ~ (∀⦗ D ⦘ (λ d → fⁱ d))
  ∃d:D．~Φ|d|→~∀d:D．Φ|d| _ _ _ _ h = h

∀d:D．|Φ|d|∧Ψ|d||⇔|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ fⁱ₂ : D → Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ₁ d ∧ fⁱ₂ d) ⇔ Γ ⊢ x ⊨ⁱ (∀⦗ D ⦘ (λ d → fⁱ₁ d)) ∧ (∀⦗ D ⦘ λ d → fⁱ₂ d)
∀d:D．|Φ|d|∧Ψ|d||⇔|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| Γ x D fⁱ₁ fⁱ₂ = ∀d:D．|Φ|d|∧Ψ|d||→|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| Γ x D fⁱ₁ fⁱ₂ , |∀d:D．Φ|d||∧|∀d:d．Ψ|d||→∀d:D．|Φ|d|∧Ψ|d|| Γ x D fⁱ₁ fⁱ₂
  where
  ∀d:D．|Φ|d|∧Ψ|d||→|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ fⁱ₂ : D → Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ₁ d ∧ fⁱ₂ d) → Γ ⊢ x ⊨ⁱ (∀⦗ D ⦘ (λ d → fⁱ₁ d)) ∧ (∀⦗ D ⦘ λ d → fⁱ₂ d)
  ∀d:D．|Φ|d|∧Ψ|d||→|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| _ _ _ _ _ (`∀ h) = `∀ (λ d → case h d of λ { (h , _) → h }) , `∀ λ d → case h d of λ { (_ , h) → h }

  |∀d:D．Φ|d||∧|∀d:d．Ψ|d||→∀d:D．|Φ|d|∧Ψ|d|| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ fⁱ₂ : D → Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (∀⦗ D ⦘ (λ d → fⁱ₁ d)) ∧ (∀⦗ D ⦘ λ d → fⁱ₂ d) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ₁ d ∧ fⁱ₂ d)
  |∀d:D．Φ|d||∧|∀d:d．Ψ|d||→∀d:D．|Φ|d|∧Ψ|d|| _ _ _ _ _ (`∀ h₁ , `∀ h₂) = `∀ λ d → h₁ d , h₂ d

∀d:D．Φ|d|→Φ|e| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev flags) → (d : D) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → fⁱ d) → Γ ⊢ x ⊨ⁱ fⁱ d
∀d:D．Φ|d|→Φ|e| _ _ _ _ d (`∀ h) = h d

-- Theorems for ∃⦗_⦘_

∃d:D．φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ _ → fⁱ) ⇔ Γ ⊢ x ⊨ⁱ fⁱ
∃d:D．φ⇔φ Γ x D fⁱ = ∃d:D．φ→φ Γ x D fⁱ , φ→∃d:D．φ Γ x D fⁱ
  where
  ∃d:D．φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ _ → fⁱ) → Γ ⊢ x ⊨ⁱ fⁱ
  ∃d:D．φ→φ _ _ _ _ (`∃ _ h) = h

  φ→∃d:D．φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ _ → fⁱ)
  φ→∃d:D．φ _ _ _ ⦃ defaultᶜ d ⦄ _ h = `∃ d h

~∃d:D．Φ|d|⇔∀d:D．~Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (∃⦗ D ⦘ λ d → fⁱ d) ⇔ Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ λ d → ~ fⁱ d
~∃d:D．Φ|d|⇔∀d:D．~Φ|d| Γ x D fⁱ = ~∃d:D．Φ|d|→∀d:D．~Φ|d| Γ x D fⁱ , ∀d:D．~Φ|d|→~∃d:D．Φ|d| Γ x D fⁱ
  where
  ~∃d:D．Φ|d|→∀d:D．~Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (∃⦗ D ⦘ λ d → fⁱ d) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ λ d → ~ fⁱ d
  ~∃d:D．Φ|d|→∀d:D．~Φ|d| _ _ _ _ h = h

  ∀d:D．~Φ|d|→~∃d:D．Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → ~ fⁱ d) → Γ ⊢ x ⊨ⁱ ~ (∃⦗ D ⦘ λ d → fⁱ d)
  ∀d:D．~Φ|d|→~∃d:D．Φ|d| _ _ _ _ h = h

∃d:D．|Φ|d|∨Ψ|d||⇔|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ fⁱ₂ : D → Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → fⁱ₁ d ∨ fⁱ₂ d) ⇔ Γ ⊢ x ⊨ⁱ (∃⦗ D ⦘ (λ d → fⁱ₁ d)) ∨ (∃⦗ D ⦘ λ d → fⁱ₂ d)
∃d:D．|Φ|d|∨Ψ|d||⇔|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| Γ x D fⁱ₁ fⁱ₂ = ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| Γ x D fⁱ₁ fⁱ₂ , |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| Γ x D fⁱ₁ fⁱ₂
  where
  ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ fⁱ₂ : D → Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → fⁱ₁ d ∨ fⁱ₂ d) → Γ ⊢ x ⊨ⁱ (∃⦗ D ⦘ (λ d → fⁱ₁ d)) ∨ (∃⦗ D ⦘ λ d → fⁱ₂ d)
  ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| _ _ _ _ _ (`∃ d (inj₁ h)) = inj₁ (`∃ d h)
  ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| _ _ _ _ _ (`∃ d (inj₂ h)) = inj₂ (`∃ d h)

  |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ fⁱ₂ : D → Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (∃⦗ D ⦘ (λ d → fⁱ₁ d)) ∨ (∃⦗ D ⦘ λ d → fⁱ₂ d) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → fⁱ₁ d ∨ fⁱ₂ d)
  |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| _ _ _ _ _ (inj₁ (`∃ d h)) = `∃ d (inj₁ h)
  |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| _ _ _ _ _ (inj₂ (`∃ d h)) = `∃ d (inj₂ h)

∃d:D．|Φ|d|∧ψ|⇔|∃d:D．Φ|d||∧ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ : D → Formulaⁱ (Shape C) ℓ prev flags) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → fⁱ₁ d ∧ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ (∃⦗ D ⦘ λ d → fⁱ₁ d) ∧ fⁱ₂
∃d:D．|Φ|d|∧ψ|⇔|∃d:D．Φ|d||∧ψ Γ x D fⁱ₁ fⁱ₂ = ∃d:D．|Φ|d|∧ψ|→|∃d:D．Φ|d||∧ψ Γ x D fⁱ₁ fⁱ₂ , |∃d:D．Φ|d||∧ψ→∃d:D．|Φ|d|∧ψ| Γ x D fⁱ₁ fⁱ₂
  where
  ∃d:D．|Φ|d|∧ψ|→|∃d:D．Φ|d||∧ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ : D → Formulaⁱ (Shape C) ℓ prev flags) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → fⁱ₁ d ∧ fⁱ₂) → Γ ⊢ x ⊨ⁱ (∃⦗ D ⦘ λ d → fⁱ₁ d) ∧ fⁱ₂
  ∃d:D．|Φ|d|∧ψ|→|∃d:D．Φ|d||∧ψ _ _ _ _ _ (`∃ d (h₁ , h₂)) = `∃ d h₁ , h₂

  |∃d:D．Φ|d||∧ψ→∃d:D．|Φ|d|∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ₁ : D → Formulaⁱ (Shape C) ℓ prev flags) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (∃⦗ D ⦘ λ d → fⁱ₁ d) ∧ fⁱ₂ → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → fⁱ₁ d ∧ fⁱ₂)
  |∃d:D．Φ|d||∧ψ→∃d:D．|Φ|d|∧ψ| _ _ _ _ _ (`∃ d h₁ , h₂) = `∃ d (h₁ , h₂)

Φ|e|→∃d:D．Φ|d| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (fⁱ : D → Formulaⁱ (Shape C) ℓ prev flags) → (d : D) → Γ ⊢ x ⊨ⁱ fⁱ d → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ λ d → fⁱ d
Φ|e|→∃d:D．Φ|d| _ _ _ _ d h = `∃ d h
