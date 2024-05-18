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
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)

open Formula

property₁ : Formula effect⁺
property₁ = ⟨ getPINˢ effect⁺ ⟩ true

proof₁ : ATMˢ ⊨ property₁
proof₁ = refl , zero , tt

property₂ : Formula effect⁺
property₂ = [ showBalanceˢ effect⁺ ] false

proof₂ : ATMˢ ⊨ property₂
proof₂ ()

property₃ : ℕ → Formula effect⁺
property₃ n = [ verifyPINˢ effect⁺ n ] false ∧ [ showBalanceˢ effect⁺ ] false ∧ [ throwExceptionˢ effect⁺ ] false

proof₃ : (n : ℕ) → ATMˢ ⊨ property₃ n
proof₃ n = (λ ()) , (λ ()) , λ ()

property₄ : ℕ → Formula effect⁺
property₄ n = ⟨ getPINˢ effect⁺ ⟩ ⟨ verifyPINˢ effect⁺ n ⟩ ⟨ showBalanceˢ effect⁺ ⟩ true

proof₄ : (n : ℕ) → ATMˢ ⊨ property₄ n
proof₄ n = refl , n , refl , true , refl , tt₀ , tt
