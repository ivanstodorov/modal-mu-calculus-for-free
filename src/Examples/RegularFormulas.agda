{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.RegularFormulas where

open import Common.RegularFormulas using (ActionFormula; RegularFormula)
open import Data.Bool using (false; true)
open import Data.Container using (Shape)
open import Data.Fin using (zero)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.FixedPoints using (proof₅)
open import Examples.Programs.ATMs-rec using (ATMˢ-rec)
open import Examples.Programs.Effect using (effect⁺)
open import ModalLogics.FixedPoints.Base using (M; mᶜ)
open import ModalLogics.RegularFormulas.Base using (Formula; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula
open RegularFormula
open M
open Formula

property : Formula (Shape effect⁺)
property = [ actF true * ] ⟨ actF true ⟩ true

proof₁ : ATMˢ-rec ⊨ property
Ni proof₁ = zero , (λ { _ _ refl → mᶜ (zero , (λ { _ false refl → proof₁
                                                 ; _ true refl → mᶜ (zero , (λ { _ _ refl → proof₁ }) , tt , tt₀ , λ { refl → mᶜ tt }) }) , tt , true , λ { refl → mᶜ tt }) }) , tt , zero , λ { refl → mᶜ tt }

proof₂ : ATMˢ-rec ⊨ property
proof₂ = proof₅
