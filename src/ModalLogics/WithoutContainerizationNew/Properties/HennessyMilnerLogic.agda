{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.HennessyMilnerLogic where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (impure; pure; free; Program)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container; Shape)
open import Data.List using (List; map)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Context; Formulaⁱ; _⊢_⊨'_; _⊢_⊨ⁱ_)
open import Relation.Binary.PropositionalEquality using (refl; inspect; sym; trans) renaming ([_] to [_]⁼)

open ActionFormula
open RegularFormula
open Formulaⁱ
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

-- Theorems for ⟨_⟩_

~⟨a⟩φ⇔[a]~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (⟨ actF act a ⟩ fⁱ) ⇔ Γ ⊢ x ⊨ⁱ [ actF act a ] ~ fⁱ
~⟨a⟩φ⇔[a]~φ Γ x a fⁱ = ~⟨a⟩φ→[a]~φ Γ x a fⁱ , [a]~φ→~⟨a⟩φ Γ x a fⁱ
  where
  ~⟨a⟩φ→[a]~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (⟨ actF act a ⟩ fⁱ) → Γ ⊢ x ⊨ⁱ [ actF act a ] ~ fⁱ
  ~⟨a⟩φ→[a]~φ _ _ _ _ h = h

  [a]~φ→~⟨a⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ [ actF act a ] ~ fⁱ → Γ ⊢ x ⊨ⁱ ~ (⟨ actF act a ⟩ fⁱ)
  [a]~φ→~⟨a⟩φ _ _ _ _ h = h

[a]false⇔false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → _⊢_⊨ⁱ_ {flags = flags} Γ x (⟨ actF act a ⟩ false) ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x false
[a]false⇔false {flags = flags} Γ x a = [a]false→false {flags = flags} Γ x a , false→[a]false {flags = flags} Γ x a
  where
  [a]false→false : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → _⊢_⊨ⁱ_ {flags = flags} Γ x (⟨ actF act a ⟩ false) → _⊢_⊨ⁱ_ {flags = flags} Γ x false
  [a]false→false _ _ _ (`⟨⟩-impure _ _ _ _ _ ())

  false→[a]false : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → _⊢_⊨ⁱ_ {flags = flags} Γ x false → _⊢_⊨ⁱ_ {flags = flags} Γ x (⟨ actF act a ⟩ false)
  false→[a]false _ _ _ ()

⟨a⟩|φ∨ψ|⇔⟨a⟩φ∨⟨a⟩ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ (fⁱ₁ ∨ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ fⁱ₁ ∨ ⟨ actF act a ⟩ fⁱ₂
⟨a⟩|φ∨ψ|⇔⟨a⟩φ∨⟨a⟩ψ Γ x a fⁱ₁ fⁱ₂ = ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ Γ x a fⁱ₁ fⁱ₂ , ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| Γ x a fⁱ₁ fⁱ₂
  where
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ (fⁱ₁ ∨ fⁱ₂) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ fⁱ₁ ∨ ⟨ actF act a ⟩ fⁱ₂
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ _ _ _ _ _ (`⟨⟩-impure s c h-eq h∈ p (inj₁ h₁)) = inj₁ (`⟨⟩-impure s c h-eq h∈ p h₁)
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ _ _ _ _ _ (`⟨⟩-impure s c h-eq h∈ p (inj₂ h₂)) = inj₂ (`⟨⟩-impure s c h-eq h∈ p h₂)

  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ fⁱ₁ ∨ ⟨ actF act a ⟩ fⁱ₂ → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ (fⁱ₁ ∨ fⁱ₂)
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| _ _ _ _ _ (inj₁ (`⟨⟩-impure s c h-eq h∈ p h₁)) = `⟨⟩-impure s c h-eq h∈ p (inj₁ h₁)
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| _ _ _ _ _ (inj₂ (`⟨⟩-impure s c h-eq h∈ p h₂)) = `⟨⟩-impure s c h-eq h∈ p (inj₂ h₂)

⟨a⟩φ∧[a]ψ→⟨a⟩|φ∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ fⁱ₁ ∧ [ actF act a ] fⁱ₂ → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ (fⁱ₁ ∧ fⁱ₂)
⟨a⟩φ∧[a]ψ→⟨a⟩|φ∧ψ| _ _ _ _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | ()
⟨a⟩φ∧[a]ψ→⟨a⟩|φ∧ψ| _ _ _ _ _ (`⟨⟩-impure s c h-eq₁ h∈ p h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (h₁ , h₂ h∈ p)

-- Theorems for [_]_

~[a]φ⇔⟨a⟩~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ ([ actF act a ] fⁱ) ⇔ Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ ~ fⁱ
~[a]φ⇔⟨a⟩~φ Γ x a fⁱ = ~[a]φ→⟨a⟩~φ Γ x a fⁱ , ⟨a⟩~φ→~[a]φ Γ x a fⁱ
  where
  ~[a]φ→⟨a⟩~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ ([ actF act a ] fⁱ) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ ~ fⁱ
  ~[a]φ→⟨a⟩~φ _ _ _ _ h = h

  ⟨a⟩~φ→~[a]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ⟨ actF act a ⟩ ~ fⁱ → Γ ⊢ x ⊨ⁱ ~ ([ actF act a ] fⁱ)
  ⟨a⟩~φ→~[a]φ _ _ _ _ h = h

[a]true⇔true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → _⊢_⊨ⁱ_ {flags = flags} Γ x ([ actF act a ] true) ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x true
[a]true⇔true {flags = flags} Γ x a = [a]true→true {flags = flags} Γ x a , true→[a]true {flags = flags} Γ x a
  where
  [a]true→true : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → _⊢_⊨ⁱ_ {flags = flags} Γ x ([ actF act a ] true) → _⊢_⊨ⁱ_ {flags = flags} Γ x true
  [a]true→true _ _ _ _ = `true

  true→[a]true : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → _⊢_⊨ⁱ_ {flags = flags} Γ x true → _⊢_⊨ⁱ_ {flags = flags} Γ x ([ actF act a ] true)
  true→[a]true _ x _ _ with free x | inspect free x
  ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
  ... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ _ → `true

[a]|φ∧ψ|⇔[a]φ∧[a]ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF act a ] (fⁱ₁ ∧ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ [ actF act a ] fⁱ₁ ∧ [ actF act a ] fⁱ₂
[a]|φ∧ψ|⇔[a]φ∧[a]ψ Γ x a fⁱ₁ fⁱ₂ = [a]|φ∧ψ|→[a]φ∧[a]ψ Γ x a fⁱ₁ fⁱ₂ , [a]φ∧[a]ψ→[a]|φ∧ψ| Γ x a fⁱ₁ fⁱ₂
  where
  [a]|φ∧ψ|→[a]φ∧[a]ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF act a ] (fⁱ₁ ∧ fⁱ₂) → Γ ⊢ x ⊨ⁱ [ actF act a ] fⁱ₁ ∧ [ actF act a ] fⁱ₂
  [a]|φ∧ψ|→[a]φ∧[a]ψ _ _ _ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq , `[]-pure r h-eq
  [a]|φ∧ψ|→[a]φ∧[a]ψ _ _ _ _ _ (`[]-impure s c h-eq h) = `[]-impure s c h-eq (λ h∈ p → case h h∈ p of λ { (h₁ , _) → h₁ }) , `[]-impure s c h-eq λ h∈ p → case h h∈ p of λ { (_ , h₂) → h₂ }

  [a]φ∧[a]ψ→[a]|φ∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (a : Shape C) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ [ actF act a ] fⁱ₁ ∧ [ actF act a ] fⁱ₂ → Γ ⊢ x ⊨ⁱ [ actF act a ] (fⁱ₁ ∧ fⁱ₂)
  [a]φ∧[a]ψ→[a]|φ∧ψ| _ _ _ _ _ (`[]-pure r h-eq , _) = `[]-pure r h-eq
  [a]φ∧[a]ψ→[a]|φ∧ψ| _ _ _ _ _ (`[]-impure _ _ _ _ , `[]-pure r h-eq) = `[]-pure r h-eq
  [a]φ∧[a]ψ→[a]|φ∧ψ| _ _ _ _ _ (`[]-impure s c h-eq₁ h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
  ... | refl = `[]-impure s c h-eq₁ λ h∈ p → h₁ h∈ p , h₂ h∈ p
