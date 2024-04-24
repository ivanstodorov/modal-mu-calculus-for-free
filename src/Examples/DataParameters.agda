{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.DataParameters where

open import Common.Injectable using ()
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ⁿ_)
open import Data.String using (String) renaming (_≟_ to _≟ˢ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Examples.Programs.BankAccountBalance using (bankAccountBalance)
open import Examples.Programs.Effect using (effect; inputS; loginS)
open import Level using (0ℓ; lift)
open import ModalLogics.DataParameters.Base using (Formula; Formulaⁱ; Quantifiedⁱ; _⊩_)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; RegularFormula)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (no; yes)

open _⊎_
open Formulaⁱ
open Quantifiedⁱ
open ActionFormula renaming (∀〔_〕_ to ∀ᵃᶠ〔_〕_; val_ to valᵃᶠ_)
open RegularFormula

property₁ : String → ℕ → Formula effect 0ℓ (inj₁ String ∷ inj₁ ℕ ∷ [])
property₁ x n = ∀〔 String 〕 λ y → ∀〔 ℕ 〕 λ m → formula val (y ≢ x ⊎ m ≢ n) ⇒ ⟨ actF act inputS effect ⟩ [ actF act loginS effect x n ] false

test₁ : (x : String) → (n : ℕ) → property₁ x n ⊩ bankAccountBalance
test₁ x n y m with x ≟ˢ y | n ≟ⁿ m
... | yes refl | yes refl = inj₁ (lift λ { (inj₁ h) → h refl
                                         ; (inj₂ h) → h refl })
... | no h | _ = inj₂ (lift refl , (y , m) , inj₂ λ { (lift refl) → h refl })
... | _ | no h = inj₂ (lift refl , (y , m) , inj₂ λ { (lift refl) → h refl })

property₂ : String → ℕ → Formula effect 0ℓ (inj₁ (String × ℕ) ∷ [])
property₂ x n = ∀〔 String × ℕ 〕 λ { (y , m) → formula val (y ≢ x ⊎ m ≢ n) ⇒ ⟨ actF act inputS effect ⟩ [ actF act loginS effect x n ] false }

test₂ : (x : String) → (n : ℕ) → property₂ x n ⊩ bankAccountBalance
test₂ x n (y , m) with x ≟ˢ y | n ≟ⁿ m
... | yes refl | yes refl = inj₁ (lift λ { (inj₁ h) → h refl
                                         ; (inj₂ h) → h refl })
... | no h | _ = inj₂ (lift refl , (y , m) , inj₂ λ { (lift refl) → h refl })
... | _ | no h = inj₂ (lift refl , (y , m) , inj₂ λ { (lift refl) → h refl })
