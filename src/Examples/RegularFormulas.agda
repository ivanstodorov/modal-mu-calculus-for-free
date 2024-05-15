{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.RegularFormulas where

open import Common.RegularFormulas using (ActionFormula; RegularFormula)
open import Data.Bool using (true; false)
open import Data.Fin using (zero)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.FixedPoints using (test₅)
open import Examples.Programs.ATMs-rec using (ATMˢ-rec)
open import Examples.Programs.Effect using (effect⁺)
open import ModalLogics.FixedPoints.Base using (M; mᶜ)
open import ModalLogics.RegularFormulas.Base using (Formula; _⊩_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula
open RegularFormula
open M
open Formula

property : Formula effect⁺
property = [ actF true * ] ⟨ actF true ⟩ true

test₁ : property ⊩ ATMˢ-rec
Ni test₁ = zero , inj₁ (tt , (λ { _ refl → mᶜ (zero , inj₁ (tt , λ { false refl → test₁
                                                                   ; true refl → mᶜ (zero , inj₁ (tt , (λ { _ refl → test₁ })) , tt , tt₀ , λ { refl → mᶜ tt }) }) , tt , true , λ { refl → mᶜ tt }) })) , tt , zero , λ { refl → mᶜ tt }

test₂ : property ⊩ ATMˢ-rec
test₂ = test₅
