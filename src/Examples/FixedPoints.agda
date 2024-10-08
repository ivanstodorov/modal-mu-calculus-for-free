{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.FixedPoints where

open import Common.Injectable using (inj)
open import Common.RegularFormulas using (ActionFormula)
open import Data.Bool using (false; true)
open import Data.Container using (Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.ATMs-rec using (ATMˢ-rec)
open import Examples.Programs.Effect using (effect⁺; IOShape)
open import ModalLogics.FixedPoints.Base using (Formula; Nu; muᶜ; nuᶜ; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula
open IOShape
open Formula
open Nu

property₁ : Formula (Shape effect⁺)
property₁ = μ "X" ． ref "X"

-- proof₁ : ATMˢ ⊨ property₁
-- proof₁ = {!   !}

property₂ : Formula (Shape effect⁺)
property₂ = ν "X" ． ref "X"

proof₂ : ATMˢ ⊨ property₂
nu proof₂ = zero , λ { refl → proof₂ }

property₃ : Formula (Shape effect⁺)
property₃ = μ "X" ． [ act inj getPIN effect⁺ ᶜ ] ref "X" ∧ ⟨ true ⟩ true

proof₃ : ATMˢ ⊨ property₃
proof₃ = muᶜ (zero , (λ h → ⊥₀-elim (h refl)) , tt , zero , λ { refl → muᶜ tt })

property₄ : Formula (Shape effect⁺)
property₄ = ν "X" ． [ true ] ref "X" ∧ ⟨ true ⟩ true

proof₄ : ATMˢ ⊨ ~ property₄
proof₄ = muᶜ (zero , tt , zero , λ { refl → muᶜ (zero , tt , false , λ { refl → muᶜ (suc zero , λ _ → ⊥₀-elim) }) })

proof₅ : ATMˢ-rec ⊨ property₄
nu proof₅ = zero , (λ { _ _ refl → nuᶜ (zero , (λ { _ false refl → proof₅
                                                  ; _ true refl → nuᶜ (zero , (λ { _ _ refl → proof₅ }) , tt , tt₀ , λ { refl → nuᶜ tt }) }) , tt , true , λ { refl → nuᶜ tt }) }) , tt , zero , λ { refl → nuᶜ tt }
