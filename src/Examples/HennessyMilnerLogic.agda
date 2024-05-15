{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.HennessyMilnerLogic where

open import Common.Injectable using ()
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.Effect using (effect⁺; getPINˢ; verifyPINˢ; showBalanceˢ; throwExceptionˢ)
open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_)
open import Relation.Binary.PropositionalEquality using (refl)

open Formula

property₁ : Formula effect⁺
property₁ = ⟨ getPINˢ effect⁺ ⟩ true

test₁ : property₁ ⊩ ATMˢ
test₁ = refl , zero , tt

property₂ : ℕ → Formula effect⁺
property₂ n = [ showBalanceˢ effect⁺ ] false

test₂ : (n : ℕ) → property₂ n ⊩ ATMˢ
test₂ n = inj₂ λ ()

property₃ : ℕ → Formula effect⁺
property₃ n = [ verifyPINˢ effect⁺ n ] false ∧ [ showBalanceˢ effect⁺ ] false ∧ [ throwExceptionˢ effect⁺ ] false

test₃ : (n : ℕ) → property₃ n ⊩ ATMˢ
test₃ n = inj₂ (λ ()) , inj₂ (λ ()) , inj₂ λ () 

property₄ : ℕ → Formula effect⁺
property₄ n = ⟨ getPINˢ effect⁺ ⟩ ⟨ verifyPINˢ effect⁺ n ⟩ ⟨ showBalanceˢ effect⁺ ⟩ true

test₄ : (n : ℕ) → property₄ n ⊩ ATMˢ
test₄ n = refl , n , refl , true , refl , tt₀ , tt
