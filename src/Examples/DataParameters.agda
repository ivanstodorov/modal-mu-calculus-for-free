{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.DataParameters where

open import Common.Injectable using ()
open import Data.Bool using (Bool; T; not)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero) renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.ATM using (ATM)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.Effect using (EffectShape; effect; effect⁺; getPINˢ; correctPINˢ)
open import Level using (0ℓ; lift)
open import ModalLogics.DataParameters.Base using (Formula; Formulaⁱ; Quantifiedⁱ; Parameterizedⁱ; M; mᶜ; []; _∷_; _⊨_)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; RegularFormula)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (no; yes)

open Bool
open EffectShape
open Formulaⁱ
open Quantifiedⁱ
open Parameterizedⁱ
open M
open ActionFormula renaming (val_ to valᵃᶠ_; ∀〔_〕_ to ∀ᵃᶠ〔_〕_)
open RegularFormula

property₁ : Formula effect 0ℓ []
property₁ = formula ⟨ actF (act getPIN) ⟩ true

proof₁ : ATM ⊨ property₁
proof₁ = lift refl , zero , tt

property₂ : Formula effect 0ℓ []
property₂ = formula [ actF (act showBalance) ] false

proof₂ : ATM ⊨ property₂
proof₂ ()

property₃ : Formula effect 0ℓ []
property₃ = formula [ actF ((act getPIN) ᶜ) ] false

proof₃ : ATM ⊨ property₃
proof₃ h = ⊥₀-elim (h (lift refl))

property₄ : Formula effect 0ℓ []
property₄ = formula ν Bool ↦ (λ b → quantified formula [ actF (act getPIN ∪ act showBalance) ᶜ ] ref zero ． (b ∷ []) ∧ [ actF act getPIN ] (val T (not b) ∧ ref zero ． (true ∷ [])) ∧ [ actF act showBalance ] (val T b ∧ ref zero ． (false ∷ []))) ． (false ∷ [])

proof₄ : ATM ⊨ property₄
Ni proof₄ = zero , (λ h → ⊥₀-elim (h (inj₁ (lift refl)))) , (λ { _ _ refl → mᶜ tt }) , (λ { _ _ refl → mᶜ (zero , (λ { _ false refl → mᶜ (zero , (λ _ ()) , (λ ()) , (λ ()) , (λ ()) , λ ())
                                                                                                                     ; _ true refl → mᶜ (zero , (λ h → ⊥₀-elim (h (inj₂ (lift refl)))) , (λ ()) , (λ ()) , (λ { _ _ refl → mᶜ tt }) , (λ { _ _ refl → proof₄ })) }) , (λ ()) , (λ ()) , (λ ()) , λ ()) }) , (λ ()) , λ ()

property₅ : ℕ → Formula effect⁺ 0ℓ (inj₁ ℕ ∷ [])
property₅ n = ∀〔 ℕ 〕 λ m → formula val (m ≢ n) ⇒ ⟨ actF act getPINˢ effect⁺ ⟩ [ actF act correctPINˢ effect⁺ n ] false

proof₅ : (n : ℕ) → ATMˢ ⊨ property₅ n
proof₅ n m with m ≟ⁿ n
... | no h = inj₂ (lift refl , m , λ { (lift refl) → ⊥₀-elim (h refl) })
... | yes refl = inj₁ (lift λ h → h refl)
