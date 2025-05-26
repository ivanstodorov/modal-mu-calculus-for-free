{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.WithoutContainerizationNew.PropertiesUnsafe.Auxiliary where

open import Common.Program using (Program)
open import Common.RegularFormulasWithData using (ActionFormula; _∈_)
open import Data.Bool using (Bool)
open import Data.Container using (Container; Shape)
open import Data.List using (List)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Context; Formulaⁱ; Formula'; _⊢_⊨'_; Formula; fⁱ→f'; _⊢_⊨ⁱ_; _⊨_)
open import Relation.Nullary using (Dec)

open Context

private variable
  a s p r ℓ : Level
  α : Set a
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

postulate
  ∈-dec : (a : α) → (af : ActionFormula α ℓ) → Dec (a ∈ af)
  ⊨'-dec : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (f' : Formula' (Shape C) ℓ prev) → Dec (Γ ⊢ x ⊨' f')

⊨ⁱ-dec : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Dec (Γ ⊢ x ⊨ⁱ fⁱ)
⊨ⁱ-dec Γ x fⁱ = ⊨'-dec Γ x (fⁱ→f' fⁱ)

⊨-dec : (x : Program C R) → (f : Formula (Shape C) ℓ) → Dec (x ⊨ f)
⊨-dec x f = ⊨ⁱ-dec [] x f
