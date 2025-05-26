{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.HennessyMilnerLogic where

open import Common.Program using (Program)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula)
open import Data.Bool using (Bool)
open import Data.Container using (Container; Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.List using (List)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Context; Formulaⁱ; _⊢_⊨'_; _⊢_⊨ⁱ_)
open import ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.Auxiliary using (⊨ⁱ-dec)
open import Relation.Nullary using (no; yes)

open ActionFormula
open RegularFormula
open Formulaⁱ
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

-- Theorems for [_]_

[a]|φ∨ψ|⇒⟨a⟩φ∨[a]ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF act a ] (fⁱ₁ ∨ fⁱ₂) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ fⁱ₁ ∨ [ actF act a ] fⁱ₂
[a]|φ∨ψ|⇒⟨a⟩φ∨[a]ψ _ _ _ _ _ (`[]-pure r h-eq) = inj₂ (`[]-pure r h-eq)
[a]|φ∨ψ|⇒⟨a⟩φ∨[a]ψ Γ x a fⁱ₁ fⁱ₂ (`[]-impure s c h-eq h) with ⊨ⁱ-dec Γ x (⟨ actF act a ⟩ fⁱ₁)
... | yes h₁ = inj₁ h₁
... | no hn₁ with ⊨ⁱ-dec Γ x ([ actF act a ] fⁱ₂)
...   | yes h₂ = inj₂ h₂
...   | no hn₂ = ⊥₀-elim (hn₂ (`[]-impure s c h-eq λ h∈ p → case h h∈ p of λ { (inj₁ h₁) → ⊥₀-elim (hn₁ (`⟨⟩-impure s c h-eq h∈ p h₁))
                                                                             ; (inj₂ h₂) → h₂ }))
