{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.RegularFormulas where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (impure; pure; free; Program)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container; Shape)
open import Data.Fin using (zero)
open import Data.List using (List; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Arguments; Context; FixedPointⁱ; FixedPoint'; Formulaⁱ; Formula'; Mu; Nu; _⊢_⊨'_; muᶜ; fⁱ→f'; rf→at; _⊢_⊨ⁱ_)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.RfConcatUtils using (⟨concatenate|at₁||at₂|⟩φ⇔⟨at₁⟩⟨at₂⟩φ; [concatenate|at₁||at₂|]φ⇔[at₁][at₂]φ)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.RfConstUtils using (⟨at⟩false→false; [at]true)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.RfDistribUtilsAll using ([at]|φ∧ψ|→[at]φ∧[at]ψ; [at]φ∧[at]ψ→[at]|φ∧ψ|)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.RfDistribUtilsEx using (⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ; ⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ|; ⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ|)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.Utils using (h-rf→at-eq; h-rf→at-just; h-rf→at-nothing)
open import Relation.Binary.PropositionalEquality using (refl; inspect; sym; trans) renaming ([_] to [_]⁼)

open ActionFormula
open RegularFormula
open List
open Arguments
open FixedPointⁱ
open FixedPoint'
open Formulaⁱ
open Formula'
open Nu
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

-- Theorems for ⟨_⟩_

⟨ε⟩φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ ε ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ fⁱ
⟨ε⟩φ⇔φ Γ x fⁱ = ⟨ε⟩φ→φ Γ x fⁱ , φ→⟨ε⟩φ Γ x fⁱ
  where
  ⟨ε⟩φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ ε ⟩ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ
  ⟨ε⟩φ→φ _ _ _ h = h

  φ→⟨ε⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ ⟨ ε ⟩ fⁱ
  φ→⟨ε⟩φ _ _ _ h = h

⟨false⟩φ⇔false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF false ⟩ fⁱ ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x false
⟨false⟩φ⇔false Γ x fⁱ = ⟨false⟩φ→false Γ x fⁱ , false→⟨false⟩φ Γ x fⁱ
  where
  ⟨false⟩φ→false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF false ⟩ fⁱ → _⊢_⊨ⁱ_ {flags = flags} Γ x false
  ⟨false⟩φ→false _ _ _ (`⟨⟩-impure _ _ _ () _ _)

  false→⟨false⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → _⊢_⊨ⁱ_ {flags = flags} Γ x false → Γ ⊢ x ⊨ⁱ ⟨ actF false ⟩ fⁱ
  false→⟨false⟩φ _ _ _ ()

⟨af₁∪af₂⟩φ⇔⟨af₁⟩φ∨⟨af₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ∪ af₂ ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ⟩ fⁱ ∨ ⟨ actF af₂ ⟩ fⁱ
⟨af₁∪af₂⟩φ⇔⟨af₁⟩φ∨⟨af₂⟩φ Γ x af₁ af₂ fⁱ = ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ Γ x af₁ af₂ fⁱ , ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ Γ x af₁ af₂ fⁱ
  where
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ∪ af₂ ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ⟩ fⁱ ∨ ⟨ actF af₂ ⟩ fⁱ
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ _ _ _ _ _ (`⟨⟩-impure s c h-eq (inj₁ h∈₁) p h) = inj₁ (`⟨⟩-impure s c h-eq h∈₁ p h)
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ _ _ _ _ _ (`⟨⟩-impure s c h-eq (inj₂ h∈₂) p h) = inj₂ (`⟨⟩-impure s c h-eq h∈₂ p h)

  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ⟩ fⁱ ∨ ⟨ actF af₂ ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ∪ af₂ ⟩ fⁱ
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ _ _ _ _ _ (inj₁ (`⟨⟩-impure s c h-eq h∈₁ p h)) = `⟨⟩-impure s c h-eq (inj₁ h∈₁) p h
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ _ _ _ _ _ (inj₂ (`⟨⟩-impure s c h-eq h∈₂ p h)) = `⟨⟩-impure s c h-eq (inj₂ h∈₂) p h

⟨af₁∩af₂⟩φ→⟨af₁⟩φ∧⟨af₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ∩ af₂ ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ⟨ actF af₁ ⟩ fⁱ ∧ ⟨ actF af₂ ⟩ fⁱ
⟨af₁∩af₂⟩φ→⟨af₁⟩φ∧⟨af₂⟩φ _ _ _ _ _ (`⟨⟩-impure s c h-eq (h∈₁ , h∈₂) p h) = `⟨⟩-impure s c h-eq h∈₁ p h , `⟨⟩-impure s c h-eq h∈₂ p h

⟨∃d:D．AF|d|⟩φ⇔∃d:D．⟨AF|d|⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF ∃⦗ D ⦘ (λ d → af d) ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ λ d → ⟨ actF af d ⟩ fⁱ
⟨∃d:D．AF|d|⟩φ⇔∃d:D．⟨AF|d|⟩φ Γ x D af fⁱ = ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ Γ x D af fⁱ , ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ Γ x D af fⁱ
  where
  ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF ∃⦗ D ⦘ (λ d → af d) ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ λ d → ⟨ actF af d ⟩ fⁱ
  ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ _ _ _ _ _ (`⟨⟩-impure s c h-eq (d , h∈) p h) = `∃ d (`⟨⟩-impure s c h-eq h∈ p h)

  ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → ⟨ actF af d ⟩ fⁱ) → Γ ⊢ x ⊨ⁱ ⟨ actF ∃⦗ D ⦘ (λ d → af d) ⟩ fⁱ
  ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ _ _ _ _ _ (`∃ d (`⟨⟩-impure s c h-eq h∈ p h)) = `⟨⟩-impure s c h-eq (d , h∈) p h

⟨∀d:D．AF|d|⟩φ→∀d:D．⟨AF|d|⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF ∀⦗ D ⦘ (λ d → af d) ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ λ d → ⟨ actF af d ⟩ fⁱ
⟨∀d:D．AF|d|⟩φ→∀d:D．⟨AF|d|⟩φ _ _ _ _ _ (`⟨⟩-impure s c h-eq h∈ p h) = `∀ λ d → `⟨⟩-impure s c h-eq (h∈ d) p h

⟨R₁+R₂⟩φ⇔⟨R₁⟩φ∨⟨R₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf₁ + rf₂ ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ ⟨ rf₁ ⟩ fⁱ ∨ ⟨ rf₂ ⟩ fⁱ
⟨R₁+R₂⟩φ⇔⟨R₁⟩φ∨⟨R₂⟩φ Γ x rf₁ rf₂ fⁱ = ⟨R₁+R₂⟩φ→⟨R₁⟩φ∨⟨R₂⟩φ Γ x rf₁ rf₂ fⁱ , ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ Γ x rf₁ rf₂ fⁱ
  where
  ⟨R₁+R₂⟩φ→⟨R₁⟩φ∨⟨R₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf₁ + rf₂ ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ⟨ rf₁ ⟩ fⁱ ∨ ⟨ rf₂ ⟩ fⁱ
  ⟨R₁+R₂⟩φ→⟨R₁⟩φ∨⟨R₂⟩φ _ _ rf₁ rf₂ _ h with rf→at rf₁ | rf→at rf₂
  ... | just _ | just _ = h
  ... | just _ | nothing = h
  ... | nothing | just _ = h
  ... | nothing | nothing = inj₁ h

  ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf₁ ⟩ fⁱ ∨ ⟨ rf₂ ⟩ fⁱ → Γ ⊢ x ⊨ⁱ ⟨ rf₁ + rf₂ ⟩ fⁱ
  ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ _ _ rf₁ rf₂ _ h with rf→at rf₁ | rf→at rf₂
  ... | just _ | just _ = h
  ... | just _ | nothing = h
  ... | nothing | just _ = h
  ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ _ _ rf₁ rf₂ _ (inj₁ h) | nothing | nothing = h
  ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ _ _ rf₁ rf₂ _ (inj₂ h) | nothing | nothing = h

⟨R₁·R₂⟩φ⇔⟨R₁⟩⟨R₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf₁ · rf₂ ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ ⟨ rf₁ ⟩ ⟨ rf₂ ⟩ fⁱ
⟨R₁·R₂⟩φ⇔⟨R₁⟩⟨R₂⟩φ Γ x rf₁ rf₂ fⁱ with rf→at rf₁
... | just at₁ with rf→at rf₂
...   | just at₂ = ⟨concatenate|at₁||at₂|⟩φ⇔⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₂ (fⁱ→f' fⁱ)
...   | nothing = (λ h → h) , λ h → h
⟨R₁·R₂⟩φ⇔⟨R₁⟩⟨R₂⟩φ Γ x rf₁ rf₂ fⁱ | nothing with rf→at rf₂
...   | just _ = (λ h → h) , λ h → h
...   | nothing = (λ h → h) , λ h → h

⟨R*⟩φ⇔μX．|⟨R⟩X∨φ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf * ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ μ [] ． formula (⟨ rf ⟩ ref zero ⦗ [] ⦘ ∨ lift fⁱ)
⟨R*⟩φ⇔μX．|⟨R⟩X∨φ| Γ x rf fⁱ = ⟨R*⟩φ→μX．|⟨R⟩X∨φ| Γ x rf fⁱ , μX．|⟨R⟩X∨φ|→⟨R*⟩φ Γ x rf fⁱ
  where
  ⟨R*⟩φ→μX．|⟨R⟩X∨φ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf * ⟩ fⁱ → Γ ⊢ x ⊨ⁱ μ [] ． formula (⟨ rf ⟩ ref zero ⦗ [] ⦘ ∨ lift fⁱ)
  ⟨R*⟩φ→μX．|⟨R⟩X∨φ| _ _ rf _ h with rf→at rf
  ... | just _ = h
  ... | nothing = `μ (muᶜ (inj₂ (`lift h)))

  μX．|⟨R⟩X∨φ|→⟨R*⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ μ [] ． formula (⟨ rf ⟩ ref zero ⦗ [] ⦘ ∨ lift fⁱ) → Γ ⊢ x ⊨ⁱ ⟨ rf * ⟩ fⁱ
  μX．|⟨R⟩X∨φ|→⟨R*⟩φ Γ x rf fⁱ h with rf→at rf
  ... | just _ = h
  μX．|⟨R⟩X∨φ|→⟨R*⟩φ {C = C} {ℓ = ℓ} {prev = prev} Γ x rf fⁱ (`μ h) | nothing = h-mu h
    where
    f' : Formula' (Shape C) ℓ prev
    f' = fⁱ→f' fⁱ

    p' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
    p' = formula (ref zero ⦗ [] ⦘ ∨ lift f')

    h-mu : Mu Γ x p' [] → Γ ⊢ x ⊨' f'
    h-mu (muᶜ (inj₁ (`ref h))) = h-mu h
    h-mu (muᶜ (inj₂ (`lift h))) = h

⟨R⁺⟩φ⇔⟨R⟩⟨R*⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf ⁺ ⟩ fⁱ ⇔ Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ ⟨ rf * ⟩ fⁱ
⟨R⁺⟩φ⇔⟨R⟩⟨R*⟩φ Γ x rf fⁱ with rf→at rf | inspect rf→at rf
... | just at₁ | [ h-eq₁ ]⁼ with rf→at (rf *) | inspect rf→at (rf *)
...   | just at₂ | [ h-eq₂ ]⁼ with h-rf→at-eq rf h-eq₁ h-eq₂
...     | refl = ⟨concatenate|at₁||at₂|⟩φ⇔⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₂ (fⁱ→f' fⁱ)
⟨R⁺⟩φ⇔⟨R⟩⟨R*⟩φ Γ x rf fⁱ | just at₁ | [ h-eq₁ ]⁼ | nothing | [ h-eq₂ ]⁼ with trans (sym (h-rf→at-just rf h-eq₁)) h-eq₂
...     | ()
⟨R⁺⟩φ⇔⟨R⟩⟨R*⟩φ Γ x rf fⁱ | nothing | [ h-eq₁ ]⁼ with rf→at (rf *) | inspect rf→at (rf *)
...   | nothing | [ h-eq₂ ]⁼ = (λ h → h) , λ h → h
...   | just at₂ | [ h-eq₂ ]⁼ with trans (sym (h-rf→at-nothing rf h-eq₁)) h-eq₂
...     | ()

~⟨R⟩φ⇔[R]~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (⟨ rf ⟩ fⁱ) ⇔ Γ ⊢ x ⊨ⁱ [ rf ] ~ fⁱ
~⟨R⟩φ⇔[R]~φ Γ x rf fⁱ = ~⟨R⟩φ→[R]~φ Γ x rf fⁱ , [R]~φ→~⟨R⟩φ Γ x rf fⁱ
  where
  ~⟨R⟩φ→[R]~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (⟨ rf ⟩ fⁱ) → Γ ⊢ x ⊨ⁱ [ rf ] ~ fⁱ
  ~⟨R⟩φ→[R]~φ _ _ rf _ h with rf→at rf
  ... | just _ = h
  ... | nothing = h

  [R]~φ→~⟨R⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ [ rf ] ~ fⁱ → Γ ⊢ x ⊨ⁱ ~ (⟨ rf ⟩ fⁱ)
  [R]~φ→~⟨R⟩φ _ _ rf _ h with rf→at rf
  ... | just _ = h
  ... | nothing = h

⟨R⟩false⇔false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → _⊢_⊨ⁱ_ {flags = flags} Γ x (⟨ rf ⟩ false) ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x false
⟨R⟩false⇔false Γ x rf with rf→at rf
... | nothing = (λ h → h) , λ h → h
... | just at = (λ h → ⟨at⟩false→false Γ x at h) , λ ()

⟨R⟩|φ∨ψ|⇔⟨R⟩φ∨⟨R⟩ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ (fⁱ₁ ∨ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ fⁱ₁ ∨ ⟨ rf ⟩ fⁱ₂
⟨R⟩|φ∨ψ|⇔⟨R⟩φ∨⟨R⟩ψ Γ x rf fⁱ₁ fⁱ₂ with rf→at rf
... | nothing = (λ h → h) , λ h → h
... | just at with fⁱ→f' fⁱ₁ | fⁱ→f' fⁱ₂
...   | f'₁ | f'₂ = ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x at f'₁ f'₂ , ⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂

⟨R⟩φ∧[R]ψ→⟨R⟩|φ∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ fⁱ₁ ∧ [ rf ] fⁱ₂ → Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ (fⁱ₁ ∧ fⁱ₂)
⟨R⟩φ∧[R]ψ→⟨R⟩|φ∧ψ| Γ x rf fⁱ₁ fⁱ₂ h with rf→at rf
... | nothing = h
... | just at = ⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x at (fⁱ→f' fⁱ₁) (fⁱ→f' fⁱ₂) h

-- Theorems for [_]_

[ε]φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ ε ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ fⁱ
[ε]φ⇔φ Γ x fⁱ = [ε]φ→φ Γ x fⁱ , φ→[ε]φ Γ x fⁱ
  where
  [ε]φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ ε ] fⁱ → Γ ⊢ x ⊨ⁱ fⁱ
  [ε]φ→φ _ _ _ h = h

  φ→[ε]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ [ ε ] fⁱ
  φ→[ε]φ _ _ _ h = h

[false]φ⇔true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF false ] fⁱ ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x true
[false]φ⇔true Γ x fⁱ = [false]φ→true Γ x fⁱ , true→[false]φ Γ x fⁱ
  where
  [false]φ→true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF false ] fⁱ → _⊢_⊨ⁱ_ {flags = flags} Γ x true
  [false]φ→true _ _ _ _ = `true

  true→[false]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → _⊢_⊨ⁱ_ {flags = flags} Γ x true → Γ ⊢ x ⊨ⁱ [ actF false ] fⁱ
  true→[false]φ _ x _ _ with free x | inspect free x
  ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
  ... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ ()

[af₁∪af₂]φ⇔[af₁]φ∧[af₁]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF af₁ ∪ af₂ ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ [ actF af₁ ] fⁱ ∧ [ actF af₂ ] fⁱ
[af₁∪af₂]φ⇔[af₁]φ∧[af₁]φ Γ x af₁ af₂ fⁱ = [af₁∪af₂]φ→[af₁]φ∧[af₁]φ Γ x af₁ af₂ fⁱ , [af₁]φ∧[af₁]φ→[af₁∪af₂]φ Γ x af₁ af₂ fⁱ
  where
  [af₁∪af₂]φ→[af₁]φ∧[af₁]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF af₁ ∪ af₂ ] fⁱ → Γ ⊢ x ⊨ⁱ [ actF af₁ ] fⁱ ∧ [ actF af₂ ] fⁱ
  [af₁∪af₂]φ→[af₁]φ∧[af₁]φ _ _ _ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq , `[]-pure r h-eq
  [af₁∪af₂]φ→[af₁]φ∧[af₁]φ _ _ _ _ _ (`[]-impure s c h-eq h) = `[]-impure s c h-eq (λ h∈₁ p → h (inj₁ h∈₁) p) , `[]-impure s c h-eq λ h∈₂ p → h (inj₂ h∈₂) p

  [af₁]φ∧[af₁]φ→[af₁∪af₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF af₁ ] fⁱ ∧ [ actF af₂ ] fⁱ → Γ ⊢ x ⊨ⁱ [ actF af₁ ∪ af₂ ] fⁱ
  [af₁]φ∧[af₁]φ→[af₁∪af₂]φ _ _ _ _ _ (`[]-pure r h-eq , _) = `[]-pure r h-eq
  [af₁]φ∧[af₁]φ→[af₁∪af₂]φ _ _ _ _ _ (`[]-impure _ _ _ _ , `[]-pure r h-eq) = `[]-pure r h-eq
  [af₁]φ∧[af₁]φ→[af₁∪af₂]φ _ _ _ _ _ (`[]-impure s c h-eq₁ h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
  ... | refl = `[]-impure s c h-eq₁ λ { (inj₁ h∈₁) p → h₁ h∈₁ p
                                      ; (inj₂ h∈₂) p → h₂ h∈₂ p }

[af₁]φ∨[af₂]φ→[af₁∩af₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF af₁ ] fⁱ ∨ [ actF af₂ ] fⁱ → Γ ⊢ x ⊨ⁱ [ actF af₁ ∩ af₂ ] fⁱ
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ _ _ _ _ _ (inj₁ (`[]-pure r h-eq)) = `[]-pure r h-eq
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ _ _ _ _ _ (inj₁ (`[]-impure s c h-eq h)) = `[]-impure s c h-eq λ h∈ p → h (proj₁ h∈) p
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ _ _ _ _ _ (inj₂ (`[]-pure r h-eq)) = `[]-pure r h-eq
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ _ _ _ _ _ (inj₂ (`[]-impure s c h-eq h)) = `[]-impure s c h-eq λ h∈ p → h (proj₂ h∈) p

[∃d:D．AF|d|]φ⇔∀d:D．[AF|d|]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF ∃⦗ D ⦘ (λ d → af d) ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ λ d → [ actF af d ] fⁱ
[∃d:D．AF|d|]φ⇔∀d:D．[AF|d|]φ Γ x D af fⁱ = [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ Γ x D af fⁱ , ∀d:D．[AF|d|]φ→[∃d:D．AF|d|]φ Γ x D af fⁱ
  where
  [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF ∃⦗ D ⦘ (λ d → af d) ] fⁱ → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ λ d → [ actF af d ] fⁱ
  [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ _ _ _ _ _ (`[]-pure r h-eq) = `∀ λ _ → `[]-pure r h-eq
  [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ _ _ _ _ _ (`[]-impure s c h-eq h) = `∀ λ d → `[]-impure s c h-eq λ h∈ p → h (d , h∈) p

  ∀d:D．[AF|d|]φ→[∃d:D．AF|d|]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∀⦗ D ⦘ (λ d → [ actF af d ] fⁱ) → Γ ⊢ x ⊨ⁱ [ actF ∃⦗ D ⦘ (λ d → af d) ] fⁱ
  ∀d:D．[AF|d|]φ→[∃d:D．AF|d|]φ _ x _ _ _ (`∀ h) with free x | inspect free x
  ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
  ... | impure (s , c) | [ h-eq₁ ]⁼ = `[]-impure s c h-eq₁ λ { (d , h∈) p → case h d of λ { (`[]-pure _ h-eq₂) → case trans (sym h-eq₁) h-eq₂ of λ ()
                                                                                          ; (`[]-impure _ _ h-eq₂ h) → case trans (sym h-eq₁) h-eq₂ of λ { refl → h h∈ p } } }

∃d:D．[AF|d|]φ→[∀d:D．AF|d|]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ∃⦗ D ⦘ (λ d → [ actF af d ] fⁱ) → Γ ⊢ x ⊨ⁱ [ actF ∀⦗ D ⦘ (λ d → af d) ] fⁱ
∃d:D．[AF|d|]φ→[∀d:D．AF|d|]φ _ _ _ _ _ (`∃ _ (`[]-pure r h-eq)) = `[]-pure r h-eq
∃d:D．[AF|d|]φ→[∀d:D．AF|d|]φ _ _ _ _ _ (`∃ d (`[]-impure s c h-eq h)) = `[]-impure s c h-eq λ h∈ p → h (h∈ d) p

[R₁+R₂]φ⇔[R₁]φ∧[R₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf₁ + rf₂ ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ [ rf₁ ] fⁱ ∧ [ rf₂ ] fⁱ
[R₁+R₂]φ⇔[R₁]φ∧[R₂]φ Γ x rf₁ rf₂ fⁱ = [R₁+R₂]φ→[R₁]φ∧[R₂]φ Γ x rf₁ rf₂ fⁱ , [R₁]φ∧[R₂]φ→[R₁+R₂]φ Γ x rf₁ rf₂ fⁱ
  where
  [R₁+R₂]φ→[R₁]φ∧[R₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf₁ + rf₂ ] fⁱ → Γ ⊢ x ⊨ⁱ [ rf₁ ] fⁱ ∧ [ rf₂ ] fⁱ
  [R₁+R₂]φ→[R₁]φ∧[R₂]φ _ _ rf₁ rf₂ _ h with rf→at rf₁ | rf→at rf₂
  ... | just _ | just _ = h
  ... | just _ | nothing = h
  ... | nothing | just _ = h
  ... | nothing | nothing = h , h

  [R₁]φ∧[R₂]φ→[R₁+R₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf₁ ] fⁱ ∧ [ rf₂ ] fⁱ → Γ ⊢ x ⊨ⁱ [ rf₁ + rf₂ ] fⁱ
  [R₁]φ∧[R₂]φ→[R₁+R₂]φ _ _ rf₁ rf₂ _ h with rf→at rf₁ | rf→at rf₂
  ... | just _ | just _ = h
  ... | just _ | nothing = h
  ... | nothing | just _ = h
  [R₁]φ∧[R₂]φ→[R₁+R₂]φ _ _ rf₁ rf₂ _ (h , _) | nothing | nothing = h

[R₁·R₂]φ⇔[R₁][R₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf₁ rf₂ : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf₁ · rf₂ ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ [ rf₁ ] [ rf₂ ] fⁱ
[R₁·R₂]φ⇔[R₁][R₂]φ Γ x rf₁ rf₂ fⁱ with rf→at rf₁
... | just at₁ with rf→at rf₂
...   | just at₂ = [concatenate|at₁||at₂|]φ⇔[at₁][at₂]φ Γ x at₁ at₂ (fⁱ→f' fⁱ)
...   | nothing = (λ h → h) , λ h → h
[R₁·R₂]φ⇔[R₁][R₂]φ Γ x rf₁ rf₂ fⁱ | nothing with rf→at rf₂
...   | just _ = (λ h → h) , λ h → h
...   | nothing = (λ h → h) , λ h → h

[R*]φ⇔νX．|[R]X∧φ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf * ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ ν [] ． formula ([ rf ] ref zero ⦗ [] ⦘ ∧ lift fⁱ)
[R*]φ⇔νX．|[R]X∧φ| Γ x rf fⁱ = [R*]φ→νX．|[R]X∧φ| Γ x rf fⁱ , νX．|[R]X∧φ|→[R*]φ Γ x rf fⁱ
  where
  [R*]φ→νX．|[R]X∧φ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf * ] fⁱ → Γ ⊢ x ⊨ⁱ ν [] ． formula ([ rf ] ref zero ⦗ [] ⦘ ∧ lift fⁱ)
  [R*]φ→νX．|[R]X∧φ| {C = C} {ℓ = ℓ} {prev = prev} Γ x rf fⁱ h with rf→at rf
  ... | just _ = h
  ... | nothing = `ν h-nu
    where
    p' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
    p' = formula (ref zero ⦗ [] ⦘ ∧ lift (fⁱ→f' fⁱ))

    h-nu : Nu Γ x p' []
    nu h-nu = `ref h-nu , `lift h

  νX．|[R]X∧φ|→[R*]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ν [] ． formula ([ rf ] ref zero ⦗ [] ⦘ ∧ lift fⁱ) → Γ ⊢ x ⊨ⁱ [ rf * ] fⁱ
  νX．|[R]X∧φ|→[R*]φ _ _ rf _ h with rf→at rf
  ... | just _ = h
  νX．|[R]X∧φ|→[R*]φ _ _ rf _ (`ν h) | nothing with nu h
  ... | _ , `lift h = h

[R⁺]φ⇔[R][R*]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf ⁺ ] fⁱ ⇔ Γ ⊢ x ⊨ⁱ [ rf ] [ rf * ] fⁱ
[R⁺]φ⇔[R][R*]φ Γ x rf fⁱ with rf→at rf | inspect rf→at rf
... | just at₁ | [ h-eq₁ ]⁼ with rf→at (rf *) | inspect rf→at (rf *)
...   | just at₂ | [ h-eq₂ ]⁼ with h-rf→at-eq rf h-eq₁ h-eq₂
...     | refl = [concatenate|at₁||at₂|]φ⇔[at₁][at₂]φ Γ x at₁ at₂ (fⁱ→f' fⁱ)
[R⁺]φ⇔[R][R*]φ Γ x rf fⁱ | just at₁ | [ h-eq₁ ]⁼ | nothing | [ h-eq₂ ]⁼ with trans (sym (h-rf→at-just rf h-eq₁)) h-eq₂
...     | ()
[R⁺]φ⇔[R][R*]φ Γ x rf fⁱ | nothing | [ h-eq₁ ]⁼ with rf→at (rf *) | inspect rf→at (rf *)
...   | nothing | [ h-eq₂ ]⁼ = (λ h → h) , λ h → h
...   | just at₂ | [ h-eq₂ ]⁼ with trans (sym (h-rf→at-nothing rf h-eq₁)) h-eq₂
...     | ()

~[R]φ⇔⟨R⟩~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ ([ rf ] fⁱ) ⇔ Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ ~ fⁱ
~[R]φ⇔⟨R⟩~φ Γ x rf fⁱ = ~[R]φ→⟨R⟩~φ Γ x rf fⁱ , ⟨R⟩~φ→~[R]φ Γ x rf fⁱ
  where
  ~[R]φ→⟨R⟩~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ ([ rf ] fⁱ) → Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ ~ fⁱ
  ~[R]φ→⟨R⟩~φ _ _ rf _ h with rf→at rf
  ... | just _ = h
  ... | nothing = h

  ⟨R⟩~φ→~[R]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ⟨ rf ⟩ ~ fⁱ → Γ ⊢ x ⊨ⁱ ~ ([ rf ] fⁱ)
  ⟨R⟩~φ→~[R]φ _ _ rf _ h with rf→at rf
  ... | just _ = h
  ... | nothing = h

[R]true⇔true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → _⊢_⊨ⁱ_ {flags = flags} Γ x ([ rf ] true) ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x true
[R]true⇔true Γ x rf with rf→at rf
... | nothing = (λ _ → `true) , λ _ → `true
... | just at = (λ _ → `true) , λ _ → [at]true Γ x at

[R]|φ∧ψ|⇔[R]φ∧[R]ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (rf : RegularFormula (Shape C) ℓ) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ rf ] (fⁱ₁ ∧ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ [ rf ] fⁱ₁ ∧ [ rf ] fⁱ₂
[R]|φ∧ψ|⇔[R]φ∧[R]ψ Γ x rf fⁱ₁ fⁱ₂ with rf→at rf
... | nothing = (λ h → h) , λ h → h
... | just at with fⁱ→f' fⁱ₁ | fⁱ→f' fⁱ₂
...   | f'₁ | f'₂ = [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at f'₁ f'₂ , [at]φ∧[at]ψ→[at]|φ∧ψ| Γ x at f'₁ f'₂

-- [R]|φ∨ψ|→⟨R⟩φ∨[R]
