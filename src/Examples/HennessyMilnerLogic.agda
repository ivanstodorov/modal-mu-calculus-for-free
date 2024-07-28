{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.HennessyMilnerLogic where

open import Common.Injectable using (inj)
open import Data.Bool using (true)
open import Data.Container using (Shape)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.Effect using (effect⁺; IOShape; VerificationShape; ExceptionShape)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)

open IOShape
open VerificationShape
open ExceptionShape
open Formula

property₁ : Formula (Shape effect⁺)
property₁ = ⟨ inj getPIN effect⁺ ⟩ true

proof₁ : ATMˢ ⊨ property₁
proof₁ = refl , zero , tt

property₂ : Formula (Shape effect⁺)
property₂ = [ inj showBalance effect⁺ ] false

proof₂ : ATMˢ ⊨ property₂
proof₂ ()

property₃ : ℕ → Formula (Shape effect⁺)
property₃ n = [ inj (correctPIN n) effect⁺ ] false ∧ [ inj showBalance effect⁺ ] false ∧ [ inj throwException effect⁺ ] false

proof₃ : (n : ℕ) → ATMˢ ⊨ property₃ n
proof₃ _ = (λ ()) , (λ ()) , λ ()

property₄ : ℕ → Formula (Shape effect⁺)
property₄ n = ⟨ inj getPIN effect⁺ ⟩ ⟨ inj (correctPIN n) effect⁺ ⟩ ⟨ inj showBalance effect⁺ ⟩ true

proof₄ : (n : ℕ) → ATMˢ ⊨ property₄ n
proof₄ n = refl , n , refl , true , refl , tt₀ , tt
