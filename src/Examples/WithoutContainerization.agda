{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.WithoutContainerization where

open import Common.Injectable using (inj)
open import Common.Program using (Program)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula)
open import Data.Bool using (Bool; not; T)
open import Data.Container using (Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Nat using (ℕ; zero; _≟_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.ATMs-rec using (ATMˢ-rec)
open import Examples.Programs.Effect using (effect⁺; IOShape; VerificationShape)
open import Level using (Level; 0ℓ; lift)
open import ModalLogics.WithoutContainerization.Base using (Formula; Formulaⁱ; Parameterizedⁱ; Arguments; Nu; nuᶜ; muᶜ; _⊨_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (no; yes)

open ActionFormula renaming (∀⦗_⦘_ to ∀ᵃᶠ⦗_⦘_; val_ to valᵃᶠ_)
open RegularFormula
open Bool
open IOShape
open VerificationShape
open Formulaⁱ
open Parameterizedⁱ
open Arguments
open Nu

private variable
  ℓ : Level

property₁ : Formula (Shape effect⁺) 0ℓ
property₁ = ⟨ actF act inj getPIN effect⁺ ⟩ true

proof₁ : ATMˢ ⊨ property₁
proof₁ = lift refl , zero , tt

property₂ : Formula (Shape effect⁺) 0ℓ
property₂ = [ actF act inj showBalance effect⁺ ] false

proof₂ : ATMˢ ⊨ property₂
proof₂ ()

property₃ : Formula (Shape effect⁺) 0ℓ
property₃ = [ actF act inj getPIN effect⁺ ᶜ ] false

proof₃ : ATMˢ ⊨ property₃
proof₃ h = ⊥₀-elim (h (lift refl))

property₄ : Formula (Shape effect⁺) 0ℓ
property₄ = ∀⦗ ℕ ⦘ λ n → ⟨ actF act inj getPIN effect⁺ ⟩ ⟨ actF act inj (correctPIN n) effect⁺ ⟩ ⟨ actF act inj showBalance effect⁺ ⟩ true

proof₄ : ATMˢ ⊨ property₄
proof₄ n = lift refl , n , lift refl , true , lift refl , tt₀ , tt

property₅ : Formula (Shape effect⁺) 0ℓ
property₅ = μ "X" ． formula ref "X" ⦗ [] ⦘

-- proof₅ : ATMˢ ⊨ property₅
-- proof₅ = {!   !}

property₆ : Formula (Shape effect⁺) 0ℓ
property₆ = ν "X" ． formula ref "X" ⦗ [] ⦘

proof₆ : {α : Set ℓ} → {x : Program effect⁺ α} → x ⊨ property₆
nu proof₆ = proof₆

property₇ : Formula (Shape effect⁺) 0ℓ
property₇ = μ "X" ． formula ([ actF act inj getPIN effect⁺ ᶜ ] ref "X" ⦗ [] ⦘ ∧ ⟨ actF true ⟩ true)

proof₇ : ATMˢ ⊨ property₇
proof₇ = muᶜ ((λ h → ⊥₀-elim (h (lift refl))) , tt , zero , tt)

property₈ : Formula (Shape effect⁺) 0ℓ
property₈ = ν "X" ． formula ([ actF true ] ref "X" ⦗ [] ⦘ ∧ ⟨ actF true ⟩ true)

proof₈' : ATMˢ ⊨ ~ property₈
proof₈' = muᶜ (inj₁ (tt , zero , muᶜ (inj₁ (tt , false , muᶜ (inj₂ λ _ ())))))

proof₈'' : ATMˢ-rec ⊨ property₈
nu proof₈'' = (λ _ _ → nuᶜ ((λ { _ false → proof₈''
                               ; _ true → nuᶜ ((λ _ _ → proof₈'') , tt , tt₀ , tt) }) , tt , true , tt)) , tt , zero , tt

property₉ : Formula (Shape effect⁺) 0ℓ
property₉ = [ actF true * ] ⟨ actF true ⟩ true

proof₉' : ATMˢ ⊨ ~ property₉
proof₉' = proof₈'

proof₉'' : ATMˢ-rec ⊨ property₉
proof₉'' = proof₈''

property₁₀ : Formula (Shape effect⁺) 0ℓ
property₁₀ = ν "X" ． Bool ＝ false ↦ λ b → formula ([ actF (act inj getPIN effect⁺ ∪ act inj showBalance effect⁺) ᶜ ] ref "X" ⦗ b ∷ [] ⦘ ∧ [ actF act inj getPIN effect⁺ ] (val T (not b) ∧ ref "X" ⦗ true ∷ [] ⦘) ∧ [ actF act inj showBalance effect⁺ ] (val T b ∧ ref "X" ⦗ false ∷ [] ⦘))

proof₁₀ : ATMˢ ⊨ property₁₀
nu proof₁₀ = (λ h → ⊥₀-elim (h (inj₁ (lift refl)))) , (λ { _ _ → tt , nuᶜ ((λ { _ false → nuᶜ ((λ _ ()) , (λ ()) , λ ())
                                                                              ; _ true → nuᶜ ((λ h → ⊥₀-elim (h (inj₂ (lift refl)))) , (λ ()) , λ _ _ → tt , proof₁₀) }) , (λ ()) , λ ()) }) , λ ()

property₁₁ : Formula (Shape effect⁺) 0ℓ
property₁₁ = ∀⦗ ℕ ⦘ λ n → ∀⦗ ℕ ⦘ λ m → val (m ≢ n) ⇒ ⟨ actF act inj getPIN effect⁺ ⟩ [ actF act inj (correctPIN n) effect⁺ ] false

proof₁₁ : ATMˢ ⊨ property₁₁
proof₁₁ n m with m ≟ n
... | no h = inj₂ (lift refl , m , λ { (lift refl) → ⊥₀-elim (h refl) })
... | yes refl = inj₁ (lift λ h → h refl)
