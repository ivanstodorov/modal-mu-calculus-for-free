{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.DataParameters where

open import Common.Injectable using ()
open import Data.Bool using (Bool; T; not)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.Effect using (effect⁺; getPINˢ; verifyPINˢ; showBalanceˢ)
open import Level using (0ℓ; lift)
open import ModalLogics.DataParameters.Base using (Formula; Formulaⁱ; Quantifiedⁱ; Parameterizedⁱ; M; mᶜ; []; _∷_; _⊩_)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; RegularFormula)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (no; yes)

open Bool
open Formulaⁱ
open Quantifiedⁱ
open Parameterizedⁱ
open M
open ActionFormula renaming (¬_ to ¬ᵃᶠ_; val_ to valᵃᶠ_; ∀〔_〕_ to ∀ᵃᶠ〔_〕_)
open RegularFormula

property₁ : Formula effect⁺ 0ℓ []
property₁ = formula ν Bool ↦ (λ b → quantified formula [ actF ¬ᵃᶠ (act getPINˢ effect⁺ ∪ act showBalanceˢ effect⁺) ] ref zero ． (b ∷ []) ∧ [ actF act getPINˢ effect⁺ ] (val T (not b) ∧ ref zero ． (true ∷ [])) ∧ [ actF act showBalanceˢ effect⁺ ] (val T b ∧ ref zero ． (false ∷ []))) ． (false ∷ [])

test₁ : property₁ ⊩ ATMˢ
Ni test₁ = zero , inj₂ (λ h → h (inj₁ (lift refl))) , inj₁ (lift refl , λ { _ refl → mᶜ tt }) , inj₁ (lift refl , λ { _ refl → mᶜ (zero , inj₁ ((λ { (inj₁ ())
                                                                                                                                                   ; (inj₂ ()) }) , λ { false refl → mᶜ (zero , inj₁ ((λ { (inj₁ ())
                                                                                                                                                                                                         ; (inj₂ ()) }) , λ ()) , (inj₂ λ ()) , (inj₂ λ ()) , (inj₂ λ ()) , inj₂ λ ())
                                                                                                                                                                      ; true refl → mᶜ (zero , inj₂ (λ h → h (inj₂ (lift refl))) , (inj₂ λ ()) , (inj₂ λ ()) , (inj₁ (lift refl , λ { _ refl → mᶜ tt })) , inj₁ (lift refl , λ { _ refl → test₁ })) }) , (inj₂ λ ()) , (inj₂ λ ()) , (inj₂ λ ()) , inj₂ λ ()) }) , (inj₂ λ ()) , inj₂ λ ()

property₂ : ℕ → Formula effect⁺ 0ℓ (inj₁ ℕ ∷ [])
property₂ n = ∀〔 ℕ 〕 λ m → formula val (m ≢ n) ⇒ ⟨ actF act getPINˢ effect⁺ ⟩ [ actF act verifyPINˢ effect⁺ n ] false

test₂ : (n : ℕ) → property₂ n ⊩ ATMˢ
test₂ n m with m ≟ⁿ n
... | no h = inj₂ (lift refl , m , inj₂ λ { (lift refl) → h refl })
... | yes refl = inj₁ (lift λ h → h refl)
