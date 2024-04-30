{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.HennessyMilnerLogic where

open import Common.Injectable using ()
open import Examples.Programs.BankAccountBalance using (bankAccountBalance)
open import Examples.Programs.Effect using (effect; getCredentialsS; loginS; showBalanceS; logoutS)
open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_)
open import Data.String using (String)
open import Data.Sum using (inj₂)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_)
open import Relation.Binary.PropositionalEquality using (refl)

open Formula

property₁ : Formula effect
property₁ = ⟨ getCredentialsS effect ⟩ true

test₁ : property₁ ⊩ bankAccountBalance
test₁ = refl , ("" , zero) , tt

property₂ : String → ℕ → Formula effect
property₂ x n = [ loginS effect x n ] false ∧ [ logoutS effect ] false

test₂ : (x : String) → (n : ℕ) → property₂ x n ⊩ bankAccountBalance
test₂ x n = inj₂ (λ ()) , inj₂ λ ()

property₃ : String → ℕ → Formula effect
property₃ x n = ⟨ getCredentialsS effect ⟩ ⟨ loginS effect x n ⟩ true

test₃ : (x : String) → (n : ℕ) → property₃ x n ⊩ bankAccountBalance
test₃ x n = refl , (x , n) , refl , true , tt

property₄ : String → ℕ → Formula effect
property₄ x n = ⟨ getCredentialsS effect ⟩ ⟨ loginS effect x n ⟩ ⟨ showBalanceS effect ⟩ ⟨ logoutS effect ⟩ true

test₄ : (x : String) → (n : ℕ) → property₄ x n ⊩ bankAccountBalance
test₄ x n = refl , (x , n) , refl , true , refl , tt₀ , refl , tt₀ , tt
