{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.FixedPoints where

open import Common.Injectable using ()
open import Common.RegularFormulas using (ActionFormula)
open import Data.Bool using (true; false)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.ATMs-rec using (ATMˢ-rec)
open import Examples.Programs.Effect using (effect⁺; getPINˢ)
open import ModalLogics.FixedPoints.Base using (Formula; M; wᶜ; mᶜ; _⊩_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula renaming (¬_ to ¬ᵃᶠ_)
open Formula
open M

property₁ : Formula effect⁺
property₁ = μ "X" ． ref "X"

-- test₁ : property₁ ⊩ ATMˢ
-- test₁ = {!   !}

property₂ : Formula effect⁺
property₂ = ν "X" ． ref "X"

test₂ : property₂ ⊩ ATMˢ
Ni test₂ = zero , λ { refl → test₂ }

property₃ : Formula effect⁺
property₃ = μ "X" ． [ ¬ᵃᶠ act getPINˢ effect⁺ ] ref "X" ∧ ⟨ true ⟩ true

test₃ : property₃ ⊩ ATMˢ
test₃ = wᶜ (zero , inj₂ (λ h → h refl) , tt , zero , λ { refl → wᶜ tt })

property₄ : Formula effect⁺
property₄ = ν "X" ． [ true ] ref "X" ∧ ⟨ true ⟩ true

test₄ : ¬ property₄ ⊩ ATMˢ
test₄ = wᶜ (zero , tt , zero , λ { refl → wᶜ (zero , tt , false , λ { refl → wᶜ (suc zero , inj₁ (tt , ⊥₀-elim)) }) })

test₅ : property₄ ⊩ ATMˢ-rec
Ni test₅ = zero , inj₁ (tt , λ { _ refl → mᶜ (zero , inj₁ (tt , λ { false refl → test₅
                                                                  ; true refl → mᶜ (zero , inj₁ (tt , λ { _ refl → test₅ }) , tt , tt₀ , λ { refl → mᶜ tt }) }) , tt , true , λ { refl → mᶜ tt }) }) , tt , zero , λ { refl → mᶜ tt }
