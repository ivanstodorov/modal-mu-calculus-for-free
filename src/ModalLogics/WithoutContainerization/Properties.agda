{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.WithoutContainerization.Properties where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula; _∈_)
open import Data.Container using (Container; Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function using (case_of_)
open import Level using (Level; lift)
open import ModalLogics.WithoutContainerization.Base using (Formula; Formulaⁱ; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; no; yes)

open ActionFormula renaming (val_ to valᵃᶠ_; ∀⦗_⦘_ to ∀ᵃᶠ⦗_⦘_; ∃⦗_⦘_ to ∃ᵃᶠ⦗_⦘_)
open RegularFormula
open Formulaⁱ renaming (val_ to valᶠ_; ∀⦗_⦘_ to ∀ᶠ⦗_⦘_; ∃⦗_⦘_ to ∃ᶠ⦗_⦘_)

private variable
  s ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  S : Set s
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ∈-dec : (s : S) → (af : ActionFormula S ℓ) → Dec (s ∈ af)
  ⊨-dec : (x : Program C α) → (f : Formula (Shape C) ℓ) → Dec (x ⊨ f)

-- Helpers

record Inhabited (α : Set ℓ) : Set ℓ where
  constructor default
  field
    a : α

-- Propositional Logic

-- Theorems for ~_

~true⇔false : (x : Program C α) → x ⊨ ~ true {ℓ = ℓ} ⇔ x ⊨ false {ℓ = ℓ}
~true⇔false {ℓ = ℓ} x = ~true→false {ℓ = ℓ} x , false→~true {ℓ = ℓ} x
  where
  ~true→false : {ℓ : Level} → (x : Program C α) → x ⊨ ~ true {ℓ = ℓ} → x ⊨ false {ℓ = ℓ}
  ~true→false _ ()

  false→~true : {ℓ : Level} → (x : Program C α) → x ⊨ false {ℓ = ℓ} → x ⊨ ~ true {ℓ = ℓ}
  false→~true _ ()

~false⇔true : (x : Program C α) → x ⊨ ~ false {ℓ = ℓ} ⇔ x ⊨ true {ℓ = ℓ}
~false⇔true {ℓ = ℓ} x = ~false→true {ℓ = ℓ} x , true→~false {ℓ = ℓ} x
  where
  ~false→true : {ℓ : Level} → (x : Program C α) → x ⊨ ~ false {ℓ = ℓ} → x ⊨ true {ℓ = ℓ}
  ~false→true _ _ = tt

  true→~false : {ℓ : Level} → (x : Program C α) → x ⊨ true {ℓ = ℓ} → x ⊨ ~ false {ℓ = ℓ}
  true→~false _ _ = tt

~|φ∧ψ|⇔|~φ|∨|~ψ| : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ~ (f₁ ∧ f₂) ⇔ x ⊨ (~ f₁) ∨ (~ f₂)
~|φ∧ψ|⇔|~φ|∨|~ψ| x f₁ f₂ = ~|φ∧ψ|→|~φ|∨|~ψ| x f₁ f₂ , |~φ|∨|~ψ|→~|φ∧ψ| x f₁ f₂
  where
  ~|φ∧ψ|→|~φ|∨|~ψ| : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ~ (f₁ ∧ f₂) → x ⊨ (~ f₁) ∨ (~ f₂)
  ~|φ∧ψ|→|~φ|∨|~ψ| _ _ _ h = h

  |~φ|∨|~ψ|→~|φ∧ψ| : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ (~ f₁) ∨ (~ f₂) → x ⊨ ~ (f₁ ∧ f₂)
  |~φ|∨|~ψ|→~|φ∧ψ| _ _ _ h = h

~|φ∨ψ|⇔|~φ|∧|~ψ| : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ~ (f₁ ∨ f₂) ⇔ x ⊨ (~ f₁) ∧ (~ f₂)
~|φ∨ψ|⇔|~φ|∧|~ψ| x f₁ f₂ = ~|φ∨ψ|→|~φ|∧|~ψ| x f₁ f₂ , |~φ|∧|~ψ|→~|φ∨ψ| x f₁ f₂
  where
  ~|φ∨ψ|→|~φ|∧|~ψ| : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ~ (f₁ ∨ f₂) → x ⊨ (~ f₁) ∧ (~ f₂)
  ~|φ∨ψ|→|~φ|∧|~ψ| _ _ _ h = h

  |~φ|∧|~ψ|→~|φ∨ψ| : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ (~ f₁) ∧ (~ f₂) → x ⊨ ~ (f₁ ∨ f₂)
  |~φ|∧|~ψ|→~|φ∨ψ| _ _ _ h = h

~~φ⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ ~ ~ f ⇔ x ⊨ f
~~φ⇔φ x f = ~~φ→φ x f , φ→~~φ x f
  where
  ~~φ→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ ~ ~ f → x ⊨ f
  ~~φ→φ _ _ h = h

  φ→~~φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ ~ ~ f
  φ→~~φ _ _ h = h

-- Theorems for _∧_

φ∧true⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∧ true ⇔ x ⊨ f
φ∧true⇔φ x f = φ∧true→φ x f , φ→φ∧true x f
  where
  φ∧true→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∧ true → x ⊨ f
  φ∧true→φ _ _ (h , _) = h

  φ→φ∧true : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ f ∧ true
  φ→φ∧true _ _ h = h , tt

φ∧false⇔false : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∧ false ⇔ x ⊨ false {ℓ = ℓ}
φ∧false⇔false x f = φ∧false→false x f , false→φ∧false x f
  where
  φ∧false→false : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∧ false → x ⊨ false {ℓ = ℓ}
  φ∧false→false _ _ ()

  false→φ∧false : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ false {ℓ = ℓ} → x ⊨ f ∧ false
  false→φ∧false _ _ () 

φ∧φ⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∧ f ⇔ x ⊨ f
φ∧φ⇔φ x f = φ∧φ→φ x f , φ→φ∧φ x f
  where
  φ∧φ→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∧ f → x ⊨ f
  φ∧φ→φ _ _ (h , _) = h

  φ→φ∧φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ f ∧ f
  φ→φ∧φ _ _ h = h , h

φ∧ψ⇔ψ∧φ : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ f₁ ∧ f₂ ⇔ x ⊨ f₂ ∧ f₁
φ∧ψ⇔ψ∧φ x f₁ f₂ = ∧-comm x f₁ f₂ , ∧-comm x f₂ f₁
  where
  ∧-comm : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ f₁ ∧ f₂ → x ⊨ f₂ ∧ f₁
  ∧-comm _ _ _ (h₁ , h₂) = h₂ , h₁

|φ∧ψ|∧χ⇔φ∧|ψ∧χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ (f₁ ∧ f₂) ∧ f₃ ⇔ x ⊨ f₁ ∧ (f₂ ∧ f₃)
|φ∧ψ|∧χ⇔φ∧|ψ∧χ| x f₁ f₂ f₃ = |φ∧ψ|∧χ→φ∧|ψ∧χ| x f₁ f₂ f₃ , φ∧|ψ∧χ|→|φ∧ψ|∧χ x f₁ f₂ f₃
  where
  |φ∧ψ|∧χ→φ∧|ψ∧χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ (f₁ ∧ f₂) ∧ f₃ → x ⊨ f₁ ∧ (f₂ ∧ f₃)
  |φ∧ψ|∧χ→φ∧|ψ∧χ| _ _ _ _ ((h₁ , h₂) , h₃) = h₁ , h₂ , h₃

  φ∧|ψ∧χ|→|φ∧ψ|∧χ : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ f₁ ∧ (f₂ ∧ f₃) → x ⊨ (f₁ ∧ f₂) ∧ f₃
  φ∧|ψ∧χ|→|φ∧ψ|∧χ _ _ _ _ (h₁ , h₂ , h₃) = (h₁ , h₂) , h₃

φ∧|ψ∨χ|⇔|φ∧ψ|∨|φ∧χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ f₁ ∧ (f₂ ∨ f₃) ⇔ x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃)
φ∧|ψ∨χ|⇔|φ∧ψ|∨|φ∧χ| x f₁ f₂ f₃ = φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| x f₁ f₂ f₃ , |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| x f₁ f₂ f₃
  where
  φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ f₁ ∧ (f₂ ∨ f₃) → x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃)
  φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| _ _ _ _ (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
  φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| _ _ _ _ (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)

  |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ (f₁ ∧ f₂) ∨ (f₁ ∧ f₃) → x ⊨ f₁ ∧ (f₂ ∨ f₃)
  |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| _ _ _ _ (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
  |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| _ _ _ _ (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

-- Theorems for _∨_

φ∨true⇔true : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∨ true ⇔ x ⊨ true {ℓ = ℓ}
φ∨true⇔true x f = φ∨true→true x f , true→φ∨true x f
  where
  φ∨true→true : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∨ true → x ⊨ true {ℓ = ℓ}
  φ∨true→true _ _ _ = tt

  true→φ∨true : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ true {ℓ = ℓ} → x ⊨ f ∨ true
  true→φ∨true _ _ _ = inj₂ tt

φ∨false⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∨ false ⇔ x ⊨ f
φ∨false⇔φ x f = φ∨false→φ x f , φ→φ∨false x f
  where
  φ∨false→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∨ false → x ⊨ f
  φ∨false→φ _ _ (inj₁ h) = h

  φ→φ∨false : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ f ∨ false
  φ→φ∨false _ _ h = inj₁ h

φ∨φ⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∨ f ⇔ x ⊨ f
φ∨φ⇔φ x f = φ∨φ→φ x f , φ→φ∨φ x f
  where
  φ∨φ→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f ∨ f → x ⊨ f
  φ∨φ→φ _ _ (inj₁ h) = h
  φ∨φ→φ _ _ (inj₂ h) = h

  φ→φ∨φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ f ∨ f
  φ→φ∨φ _ _ h = inj₁ h

φ∨ψ⇔ψ∨φ : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ f₁ ∨ f₂ ⇔ x ⊨ f₂ ∨ f₁
φ∨ψ⇔ψ∨φ x f₁ f₂ = ∨-comm x f₁ f₂ , ∨-comm x f₂ f₁
  where
  ∨-comm : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ f₁ ∨ f₂ → x ⊨ f₂ ∨ f₁
  ∨-comm _ _ _ (inj₁ h₁) = inj₂ h₁
  ∨-comm _ _ _ (inj₂ h₂) = inj₁ h₂

|φ∨ψ|∨χ⇔φ∨|ψ∨χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ (f₁ ∨ f₂) ∨ f₃ ⇔ x ⊨ f₁ ∨ (f₂ ∨ f₃)
|φ∨ψ|∨χ⇔φ∨|ψ∨χ| x f₁ f₂ f₃ = |φ∨ψ|∨χ→φ∨|ψ∨χ| x f₁ f₂ f₃ , φ∨|ψ∨χ|→|φ∨ψ|∨χ x f₁ f₂ f₃
  where
  |φ∨ψ|∨χ→φ∨|ψ∨χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ (f₁ ∨ f₂) ∨ f₃ → x ⊨ f₁ ∨ (f₂ ∨ f₃)
  |φ∨ψ|∨χ→φ∨|ψ∨χ| _ _ _ _ (inj₁ (inj₁ h₁)) = inj₁ h₁
  |φ∨ψ|∨χ→φ∨|ψ∨χ| _ _ _ _ (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
  |φ∨ψ|∨χ→φ∨|ψ∨χ| _ _ _ _ (inj₂ h₃) = inj₂ (inj₂ h₃)

  φ∨|ψ∨χ|→|φ∨ψ|∨χ : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ f₁ ∨ (f₂ ∨ f₃) → x ⊨ (f₁ ∨ f₂) ∨ f₃
  φ∨|ψ∨χ|→|φ∨ψ|∨χ _ _ _ _ (inj₁ h₁) = inj₁ (inj₁ h₁)
  φ∨|ψ∨χ|→|φ∨ψ|∨χ _ _ _ _ (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
  φ∨|ψ∨χ|→|φ∨ψ|∨χ _ _ _ _ (inj₂ (inj₂ h₃)) = inj₂ h₃

φ∨|ψ∧χ|⇔|φ∨ψ|∧|φ∨χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ f₁ ∨ (f₂ ∧ f₃) ⇔ x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃)
φ∨|ψ∧χ|⇔|φ∨ψ|∧|φ∨χ| x f₁ f₂ f₃ = φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| x f₁ f₂ f₃ , |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| x f₁ f₂ f₃
  where
  φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ f₁ ∨ (f₂ ∧ f₃) → x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃)
  φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| _ _ _ _ (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
  φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| _ _ _ _ (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃

  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| : (x : Program C α) → (f₁ f₂ f₃ : Formula (Shape C) ℓ) → x ⊨ (f₁ ∨ f₂) ∧ (f₁ ∨ f₃) → x ⊨ f₁ ∨ (f₂ ∧ f₃)
  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| _ _ _ _ (inj₁ h₁ , _) = inj₁ h₁
  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| _ _ _ _ (_ , inj₁ h₁) = inj₁ h₁
  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| _ _ _ _ (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

-- Theorems for _⇒_

φ⇒ψ⇔|~φ|∨ψ : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ f₁ ⇒ f₂ ⇔ x ⊨ (~ f₁) ∨ f₂
φ⇒ψ⇔|~φ|∨ψ x f₁ f₂ = φ⇒ψ→|~φ|∨ψ x f₁ f₂ , |~φ|∨ψ→φ⇒ψ x f₁ f₂
  where
  φ⇒ψ→|~φ|∨ψ : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ f₁ ⇒ f₂ → x ⊨ (~ f₁) ∨ f₂
  φ⇒ψ→|~φ|∨ψ _ _ _ h = h

  |~φ|∨ψ→φ⇒ψ : (x : Program C α) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ (~ f₁) ∨ f₂ → x ⊨ f₁ ⇒ f₂
  |~φ|∨ψ→φ⇒ψ _ _ _ h = h

-- Predicate Logic

-- Theorems for ∀⦗_⦘_

∀d:D．φ⇔φ : (x : Program C α) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (f : Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ _ → f) ⇔ x ⊨ f
∀d:D．φ⇔φ x D f = ∀d:D．φ→φ x D f , φ→∀d:D．φ x D f
  where
  ∀d:D．φ→φ : (x : Program C α) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (f : Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ _ → f) → x ⊨ f
  ∀d:D．φ→φ _ _ ⦃ default d ⦄ _ h∀ = h∀ d

  φ→∀d:D．φ : (x : Program C α) → (D : Set ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ ∀ᶠ⦗ D ⦘ λ _ → f
  φ→∀d:D．φ _ _ _ h _ = h

~∀d:D．Φ|d|⇔∃d:D．~Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → x ⊨ ~ (∀ᶠ⦗ D ⦘ λ d → f d) ⇔ x ⊨ ∃ᶠ⦗ D ⦘ λ d → ~ f d
~∀d:D．Φ|d|⇔∃d:D．~Φ|d| x D f = ~∀d:D．Φ|d|→∃d:D．~Φ|d| x D f , ∃d:D．~Φ|d|→~∀d:D．Φ|d| x D f
  where
  ~∀d:D．Φ|d|→∃d:D．~Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → x ⊨ ~ (∀ᶠ⦗ D ⦘ λ d → f d) → x ⊨ ∃ᶠ⦗ D ⦘ λ d → ~ f d
  ~∀d:D．Φ|d|→∃d:D．~Φ|d| _ _ _ h = h

  ∃d:D．~Φ|d|→~∀d:D．Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → ~ f d) → x ⊨ ~ (∀ᶠ⦗ D ⦘ λ d → f d)
  ∃d:D．~Φ|d|→~∀d:D．Φ|d| _ _ _ h = h

∀d:D．|Φ|d|∧Ψ|d||⇔|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| : (x : Program C α) → (D : Set ℓ) → (f₁ f₂ : D → Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f₁ d ∧ f₂ d) ⇔ x ⊨ (∀ᶠ⦗ D ⦘ (λ d → f₁ d)) ∧ (∀ᶠ⦗ D ⦘ λ d → f₂ d)
∀d:D．|Φ|d|∧Ψ|d||⇔|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| x D f₁ f₂ = ∀d:D．|Φ|d|∧Ψ|d||→|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| x D f₁ f₂ , |∀d:D．Φ|d||∧|∀d:d．Ψ|d||→∀d:D．|Φ|d|∧Ψ|d|| x D f₁ f₂
  where
  ∀d:D．|Φ|d|∧Ψ|d||→|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| : (x : Program C α) → (D : Set ℓ) → (f₁ f₂ : D → Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f₁ d ∧ f₂ d) → x ⊨ (∀ᶠ⦗ D ⦘ (λ d → f₁ d)) ∧ (∀ᶠ⦗ D ⦘ λ d → f₂ d)
  ∀d:D．|Φ|d|∧Ψ|d||→|∀d:D．Φ|d||∧|∀d:d．Ψ|d|| _ _ _ _ h = (λ d → proj₁ (h d)) , λ d → proj₂ (h d)

  |∀d:D．Φ|d||∧|∀d:d．Ψ|d||→∀d:D．|Φ|d|∧Ψ|d|| : (x : Program C α) → (D : Set ℓ) → (f₁ f₂ : D → Formula (Shape C) ℓ) → x ⊨ (∀ᶠ⦗ D ⦘ (λ d → f₁ d)) ∧ (∀ᶠ⦗ D ⦘ λ d → f₂ d) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f₁ d ∧ f₂ d)
  |∀d:D．Φ|d||∧|∀d:d．Ψ|d||→∀d:D．|Φ|d|∧Ψ|d|| _ _ _ _ (h₁ , h₂) d = h₁ d , h₂ d

∀d:D．|Φ|d|∨ψ|⇔|∀d:D．Φ|d||∨ψ : (x : Program C α) → (D : Set ℓ) → (f₁ : D → Formula (Shape C) ℓ) → (f₂ : Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f₁ d ∨ f₂) ⇔ x ⊨ (∀ᶠ⦗ D ⦘ λ d → f₁ d) ∨ f₂
∀d:D．|Φ|d|∨ψ|⇔|∀d:D．Φ|d||∨ψ x D f₁ f₂ = ∀d:D．|Φ|d|∨ψ|→|∀d:D．Φ|d||∨ψ x D f₁ f₂ , |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| x D f₁ f₂
  where
  ∀d:D．|Φ|d|∨ψ|→|∀d:D．Φ|d||∨ψ : (x : Program C α) → (D : Set ℓ) → (f₁ : D → Formula (Shape C) ℓ) → (f₂ : Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f₁ d ∨ f₂) → x ⊨ (∀ᶠ⦗ D ⦘ λ d → f₁ d) ∨ f₂
  ∀d:D．|Φ|d|∨ψ|→|∀d:D．Φ|d||∨ψ x _ _ f₂ h with ⊨-dec x f₂
  ... | yes h₂ = inj₂ h₂
  ... | no hn₂ = inj₁ λ d → case h d of λ { (inj₁ h₁) → h₁
                                          ; (inj₂ h₂) → ⊥₀-elim (hn₂ h₂) }

  |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| : (x : Program C α) → (D : Set ℓ) → (f₁ : D → Formula (Shape C) ℓ) → (f₂ : Formula (Shape C) ℓ) → x ⊨ (∀ᶠ⦗ D ⦘ λ d → f₁ d) ∨ f₂ → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f₁ d ∨ f₂)
  |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| _ _ _ _ (inj₁ h₁) d = inj₁ (h₁ d)
  |∀d:D．Φ|d||∨ψ→∀d:D．|Φ|d|∨ψ| _ _ _ _ (inj₂ h₂) _ = inj₂ h₂

∀d:D．Φ|d|→Φ|e| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → (e : D) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → f d) → x ⊨ f e
∀d:D．Φ|d|→Φ|e| _ _ _ d h = h d

-- Theorems for ∃⦗_⦘_

∃d:D．φ⇔φ : (x : Program C α) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (f : Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ _ → f) ⇔ x ⊨ f
∃d:D．φ⇔φ x D f = ∃d:D．φ→φ x D f , φ→∃d:D．φ x D f
  where
  ∃d:D．φ→φ : (x : Program C α) → (D : Set ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ _ → f) → x ⊨ f
  ∃d:D．φ→φ _ _ _ (_ , h) = h

  φ→∃d:D．φ : (x : Program C α) → (D : Set ℓ) → ⦃ Inhabited D ⦄ → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ ∃ᶠ⦗ D ⦘ (λ _ → f)
  φ→∃d:D．φ _ _ ⦃ default d ⦄ _ h = d , h

~∃d:D．Φ|d|⇔∀d:D．~Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → x ⊨ ~ (∃ᶠ⦗ D ⦘ λ d → f d) ⇔ x ⊨ ∀ᶠ⦗ D ⦘ λ d → ~ f d
~∃d:D．Φ|d|⇔∀d:D．~Φ|d| x D f = ~∃d:D．Φ|d|→∀d:D．~Φ|d| x D f , ∀d:D．~Φ|d|→~∃d:D．Φ|d| x D f
  where
  ~∃d:D．Φ|d|→∀d:D．~Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → x ⊨ ~ (∃ᶠ⦗ D ⦘ λ d → f d) → x ⊨ ∀ᶠ⦗ D ⦘ λ d → ~ f d
  ~∃d:D．Φ|d|→∀d:D．~Φ|d| _ _ _ h = h

  ∀d:D．~Φ|d|→~∃d:D．Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → ~ f d) → x ⊨ ~ (∃ᶠ⦗ D ⦘ λ d → f d)
  ∀d:D．~Φ|d|→~∃d:D．Φ|d| _ _ _ h = h

∃d:D．|Φ|d|∨Ψ|d||⇔|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| : (x : Program C α) → (D : Set ℓ) → (f₁ f₂ : D → Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f₁ d ∨ f₂ d) ⇔ x ⊨ (∃ᶠ⦗ D ⦘ (λ d → f₁ d)) ∨ (∃ᶠ⦗ D ⦘ λ d → f₂ d)
∃d:D．|Φ|d|∨Ψ|d||⇔|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| x D f₁ f₂ = ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| x D f₁ f₂ , |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| x D f₁ f₂
  where
  ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| : (x : Program C α) → (D : Set ℓ) → (f₁ f₂ : D → Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f₁ d ∨ f₂ d) → x ⊨ (∃ᶠ⦗ D ⦘ (λ d → f₁ d)) ∨ (∃ᶠ⦗ D ⦘ λ d → f₂ d)
  ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| _ _ _ _ (d , inj₁ h₁) = inj₁ (d , h₁)
  ∃d:D．|Φ|d|∨Ψ|d||→|∃d:D．Φ|d||∨|∃d:d．Ψ|d|| _ _ _ _ (d , inj₂ h₂) = inj₂ (d , h₂)

  |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| : (x : Program C α) → (D : Set ℓ) → (f₁ f₂ : D → Formula (Shape C) ℓ) → x ⊨ (∃ᶠ⦗ D ⦘ (λ d → f₁ d)) ∨ (∃ᶠ⦗ D ⦘ λ d → f₂ d) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f₁ d ∨ f₂ d)
  |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| _ _ _ _ (inj₁ (d , h₁)) = d , inj₁ h₁
  |∃d:D．Φ|d||∨|∃d:d．Ψ|d||→∃d:D．|Φ|d|∨Ψ|d|| _ _ _ _ (inj₂ (d , h₂)) = d , inj₂ h₂

∃d:D．|Φ|d|∧ψ|⇔|∃d:D．Φ|d||∧ψ : (x : Program C α) → (D : Set ℓ) → (f₁ : D → Formula (Shape C) ℓ) → (f₂ : Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f₁ d ∧ f₂) ⇔ x ⊨ (∃ᶠ⦗ D ⦘ λ d → f₁ d) ∧ f₂
∃d:D．|Φ|d|∧ψ|⇔|∃d:D．Φ|d||∧ψ x D f₁ f₂ = ∃d:D．|Φ|d|∧ψ|→|∃d:D．Φ|d||∧ψ x D f₁ f₂ , |∃d:D．Φ|d||∧ψ→∃d:D．|Φ|d|∧ψ| x D f₁ f₂
  where
  ∃d:D．|Φ|d|∧ψ|→|∃d:D．Φ|d||∧ψ : (x : Program C α) → (D : Set ℓ) → (f₁ : D → Formula (Shape C) ℓ) → (f₂ : Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f₁ d ∧ f₂) → x ⊨ (∃ᶠ⦗ D ⦘ λ d → f₁ d) ∧ f₂
  ∃d:D．|Φ|d|∧ψ|→|∃d:D．Φ|d||∧ψ _ _ _ _ (d , h₁ , h₂) = (d , h₁) , h₂

  |∃d:D．Φ|d||∧ψ→∃d:D．|Φ|d|∧ψ| : (x : Program C α) → (D : Set ℓ) → (f₁ : D → Formula (Shape C) ℓ) → (f₂ : Formula (Shape C) ℓ) → x ⊨ (∃ᶠ⦗ D ⦘ λ d → f₁ d) ∧ f₂ → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f₁ d ∧ f₂)
  |∃d:D．Φ|d||∧ψ→∃d:D．|Φ|d|∧ψ| _ _ _ _ ((d , h₁) , h₂) = d , h₁ , h₂

Φ|e|→∃d:D．Φ|d| : (x : Program C α) → (D : Set ℓ) → (f : D → Formula (Shape C) ℓ) → (e : D) → x ⊨ f e → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → f d)
Φ|e|→∃d:D．Φ|d| _ _ _ d h = d , h

-- Action Formulas

trueᶜ⇔false : {ℓ : Level} → (s : S) → s ∈ true {ℓ = ℓ} ᶜ ⇔ s ∈ false {ℓ = ℓ}
trueᶜ⇔false {ℓ = ℓ} s = trueᶜ→false {ℓ = ℓ} s , false→trueᶜ {ℓ = ℓ} s
  where
  trueᶜ→false : {ℓ : Level} → (s : S) → s ∈ true {ℓ = ℓ} ᶜ → s ∈ false {ℓ = ℓ}
  trueᶜ→false _ h = ⊥₀-elim (h tt)

  false→trueᶜ : {ℓ : Level} → (s : S) → s ∈ false {ℓ = ℓ} → s ∈ true {ℓ = ℓ} ᶜ
  false→trueᶜ _ ()

falseᶜ⇔true : {ℓ : Level} → (s : S) → s ∈ false {ℓ = ℓ} ᶜ ⇔ s ∈ true {ℓ = ℓ}
falseᶜ⇔true {ℓ = ℓ} s = falseᶜ→true {ℓ = ℓ} s , true→falseᶜ {ℓ = ℓ} s
  where
  falseᶜ→true : {ℓ : Level} → (s : S) → s ∈ false {ℓ = ℓ} ᶜ → s ∈ true {ℓ = ℓ}
  falseᶜ→true _ _ = tt

  true→falseᶜ : {ℓ : Level} → (s : S) → s ∈ true {ℓ = ℓ} → s ∈ false {ℓ = ℓ} ᶜ
  true→falseᶜ _ _ ()

|α₁∪α₂|ᶜ⇔|α₁ᶜ|∩|α₂ᶜ| : (s : S) → (α₁ α₂ : ActionFormula S ℓ) → s ∈ (α₁ ∪ α₂) ᶜ ⇔ s ∈ (α₁ ᶜ) ∩ (α₂ ᶜ)
|α₁∪α₂|ᶜ⇔|α₁ᶜ|∩|α₂ᶜ| s α₁ α₂ = |α₁∪α₂|ᶜ→|α₁ᶜ|∩|α₂ᶜ| s α₁ α₂ , |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ s α₁ α₂
  where
  |α₁∪α₂|ᶜ→|α₁ᶜ|∩|α₂ᶜ| : (s : S) → (α₁ α₂ : ActionFormula S ℓ) → s ∈ (α₁ ∪ α₂) ᶜ → s ∈ (α₁ ᶜ) ∩ (α₂ ᶜ)
  |α₁∪α₂|ᶜ→|α₁ᶜ|∩|α₂ᶜ| s α₁ α₂ h with ∈-dec s α₁
  ... | yes h₁ = ⊥₀-elim (h (inj₁ h₁))
  ... | no hn₁ with ∈-dec s α₂
  ...   | yes h₂ = ⊥₀-elim (h (inj₂ h₂))
  ...   | no hn₂ = hn₁ , hn₂

  |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ : (s : S) → (α₁ α₂ : ActionFormula S ℓ) → s ∈ (α₁ ᶜ) ∩ (α₂ ᶜ) → s ∈ (α₁ ∪ α₂) ᶜ
  |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ _ _ _ (hn₁ , _) (inj₁ h₁) = hn₁ h₁
  |α₁ᶜ|∩|α₂ᶜ|→|α₁∪α₂|ᶜ _ _ _ (_ , hn₂) (inj₂ h₂) = hn₂ h₂

|α₁∩α₂|ᶜ⇔|α₁ᶜ|∪|α₂ᶜ| : (s : S) → (α₁ α₂ : ActionFormula S ℓ) → s ∈ (α₁ ∩ α₂) ᶜ ⇔ s ∈ (α₁ ᶜ) ∪ (α₂ ᶜ)
|α₁∩α₂|ᶜ⇔|α₁ᶜ|∪|α₂ᶜ| s α₁ α₂ = |α₁∩α₂|ᶜ→|α₁ᶜ|∪|α₂ᶜ| s α₁ α₂ , |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ s α₁ α₂
  where
  |α₁∩α₂|ᶜ→|α₁ᶜ|∪|α₂ᶜ| : (s : S) → (α₁ α₂ : ActionFormula S ℓ) → s ∈ (α₁ ∩ α₂) ᶜ → s ∈ (α₁ ᶜ) ∪ (α₂ ᶜ)
  |α₁∩α₂|ᶜ→|α₁ᶜ|∪|α₂ᶜ| s α₁ α₂ h with ∈-dec s α₁
  ... | no hn₁ = inj₁ hn₁
  ... | yes h₁ with ∈-dec s α₂
  ...   | no hn₂ = inj₂ hn₂
  ...   | yes h₂ = ⊥₀-elim (h (h₁ , h₂))

  |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ : (s : S) → (α₁ α₂ : ActionFormula S ℓ) → s ∈ (α₁ ᶜ) ∪ (α₂ ᶜ) → s ∈ (α₁ ∩ α₂) ᶜ
  |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ _ _ _ (inj₁ hn₁) (h₁ , _) = hn₁ h₁
  |α₁ᶜ|∪|α₂ᶜ|→|α₁∩α₂|ᶜ _ _ _ (inj₂ hn₂) (_ , h₂) = hn₂ h₂

|∃d:D．A|d||ᶜ⇔∀d:D．|A|d||ᶜ : (s : S) → (D : Set ℓ) → (α : D → ActionFormula S ℓ) → s ∈ (∃ᵃᶠ⦗ D ⦘ λ d → α d) ᶜ ⇔ s ∈ ∀ᵃᶠ⦗ D ⦘ λ d → α d ᶜ
|∃d:D．A|d||ᶜ⇔∀d:D．|A|d||ᶜ s D α = |∃d:D．A|d||ᶜ→∀d:D．|A|d||ᶜ s D α , ∀d:D．|A|d||ᶜ→|∃d:D．A|d||ᶜ s D α
  where
  |∃d:D．A|d||ᶜ→∀d:D．|A|d||ᶜ : (s : S) → (D : Set ℓ) → (α : D → ActionFormula S ℓ) → s ∈ (∃ᵃᶠ⦗ D ⦘ λ d → α d) ᶜ → s ∈ ∀ᵃᶠ⦗ D ⦘ λ d → α d ᶜ
  |∃d:D．A|d||ᶜ→∀d:D．|A|d||ᶜ _ _ _ hn∃ d h = hn∃ (d , h)

  ∀d:D．|A|d||ᶜ→|∃d:D．A|d||ᶜ : (s : S) → (D : Set ℓ) → (α : D → ActionFormula S ℓ) → s ∈ ∀ᵃᶠ⦗ D ⦘ (λ d → α d ᶜ) → s ∈ (∃ᵃᶠ⦗ D ⦘ λ d → α d) ᶜ
  ∀d:D．|A|d||ᶜ→|∃d:D．A|d||ᶜ _ _ _ h∀ (d , h) = (h∀ d) h

|∀d:D．A|d||ᶜ⇔∃d:D．|A|d||ᶜ : (s : S) → (D : Set ℓ) → (α : D → ActionFormula S ℓ) → s ∈ (∀ᵃᶠ⦗ D ⦘ λ d → α d) ᶜ ⇔ s ∈ ∃ᵃᶠ⦗ D ⦘ λ d → α d ᶜ
|∀d:D．A|d||ᶜ⇔∃d:D．|A|d||ᶜ s D α = |∀d:D．A|d||ᶜ→∃d:D．|A|d||ᶜ s D α , ∃d:D．|A|d||ᶜ→|∀d:D．A|d||ᶜ s D α
  where
  |∀d:D．A|d||ᶜ→∃d:D．|A|d||ᶜ : (s : S) → (D : Set ℓ) → (α : D → ActionFormula S ℓ) → s ∈ (∀ᵃᶠ⦗ D ⦘ λ d → α d) ᶜ → s ∈ ∃ᵃᶠ⦗ D ⦘ λ d → α d ᶜ
  |∀d:D．A|d||ᶜ→∃d:D．|A|d||ᶜ s D α hn∀ with ∈-dec s (∃ᵃᶠ⦗ D ⦘ λ d → α d ᶜ)
  ... | yes h∃ = h∃
  ... | no hn∃ = ⊥₀-elim (hn∀ λ d → case ∈-dec s (α d) of λ { (yes h) → h
                                                            ; (no hn) → ⊥₀-elim (hn∃ (d , hn)) })

  ∃d:D．|A|d||ᶜ→|∀d:D．A|d||ᶜ : (s : S) → (D : Set ℓ) → (α : D → ActionFormula S ℓ) → s ∈ ∃ᵃᶠ⦗ D ⦘ (λ d → α d ᶜ) → s ∈ (∀ᵃᶠ⦗ D ⦘ λ d → α d) ᶜ
  ∃d:D．|A|d||ᶜ→|∀d:D．A|d||ᶜ _ _ _ (d , hn) h = hn (h d)

-- Hennessy-Milner Logic

-- Theorems for ⟨_⟩_

~⟨a⟩φ⇔[a]~φ : (x : Program C α) → (a : Shape C) → (f : Formula (Shape C) ℓ) → x ⊨ ~ (⟨ actF act a ⟩ f) ⇔ x ⊨ [ actF act a ] ~ f
~⟨a⟩φ⇔[a]~φ x a f = ~⟨a⟩φ→[a]~φ x a f , [a]~φ→~⟨a⟩φ x a f
  where
  ~⟨a⟩φ→[a]~φ : (x : Program C α) → (a : Shape C) → (f : Formula (Shape C) ℓ) → x ⊨ ~ (⟨ actF act a ⟩ f) → x ⊨ [ actF act a ] ~ f
  ~⟨a⟩φ→[a]~φ _ _ _ h = h

  [a]~φ→~⟨a⟩φ : (x : Program C α) → (a : Shape C) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF act a ] ~ f → x ⊨ ~ (⟨ actF act a ⟩ f)
  [a]~φ→~⟨a⟩φ _ _ _ h = h

[a]false⇔false : (x : Program C α) → (a : Shape C) → x ⊨ ⟨ actF act a ⟩ false {ℓ = ℓ} ⇔ x ⊨ false {ℓ = ℓ}
[a]false⇔false x a = [a]false→false x a , false→[a]false x a
  where
  [a]false→false : (x : Program C α) → (a : Shape C) → x ⊨ ⟨ actF act a ⟩ false {ℓ = ℓ} → x ⊨ false {ℓ = ℓ}
  [a]false→false x _ h with free x
  [a]false→false x _ () | pure _
  [a]false→false x _ () | impure (s , c)

  false→[a]false : (x : Program C α) → (a : Shape C) → x ⊨ false {ℓ = ℓ} → x ⊨ ⟨ actF act a ⟩ false {ℓ = ℓ}
  false→[a]false _ _ ()

⟨a⟩|φ∨ψ|⇔⟨a⟩φ∨⟨a⟩ψ : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ⟨ actF act a ⟩ (f₁ ∨ f₂) ⇔ x ⊨ ⟨ actF act a ⟩ f₁ ∨ ⟨ actF act a ⟩ f₂
⟨a⟩|φ∨ψ|⇔⟨a⟩φ∨⟨a⟩ψ x a f₁ f₂ = ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ x a f₁ f₂ , ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| x a f₁ f₂
  where
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ⟨ actF act a ⟩ (f₁ ∨ f₂) → x ⊨ ⟨ actF act a ⟩ f₁ ∨ ⟨ actF act a ⟩ f₂
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ x _ _ _ h with free x
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ x _ _ _ (lift refl , r , inj₁ h₁) | impure _ = inj₁ (lift refl , r , h₁)
  ⟨a⟩|φ∨ψ|→⟨a⟩φ∨⟨a⟩ψ x _ _ _ (lift refl , r , inj₂ h₂) | impure _ = inj₂ (lift refl , r , h₂)

  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ⟨ actF act a ⟩ f₁ ∨ ⟨ actF act a ⟩ f₂ → x ⊨ ⟨ actF act a ⟩ (f₁ ∨ f₂)
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| x _ _ _ h with free x
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| x _ _ _ (inj₁ ()) | pure _
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| x _ _ _ (inj₂ ()) | pure _
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| x _ _ _ (inj₁ (lift refl , r , h₁)) | impure _ = lift refl , r , inj₁ h₁
  ⟨a⟩φ∨⟨a⟩ψ→⟨a⟩|φ∨ψ| x _ _ _ (inj₂ (lift refl , r , h₂)) | impure _ = lift refl , r , inj₂ h₂

⟨a⟩φ∧[a]ψ→⟨a⟩|φ∧ψ| : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ ⟨ actF act a ⟩ f₁ ∧ [ actF act a ] f₂ → x ⊨ ⟨ actF act a ⟩ (f₁ ∧ f₂)
⟨a⟩φ∧[a]ψ→⟨a⟩|φ∧ψ| x _ _ _ h with free x
⟨a⟩φ∧[a]ψ→⟨a⟩|φ∧ψ| x _ _ _ ((lift refl , r , h₁) , h₂) | impure _ = lift refl , r , h₁ , h₂ (lift refl) r

-- Theorems for [_]_

~[a]φ⇔⟨a⟩~φ : (x : Program C α) → (a : Shape C) → (f : Formula (Shape C) ℓ) → x ⊨ ~ ([ actF act a ] f) ⇔ x ⊨ ⟨ actF act a ⟩ ~ f
~[a]φ⇔⟨a⟩~φ x a f = ~[a]φ→⟨a⟩~φ x a f , ⟨a⟩~φ→~[a]φ x a f
  where
  ~[a]φ→⟨a⟩~φ : (x : Program C α) → (a : Shape C) → (f : Formula (Shape C) ℓ) → x ⊨ ~ ([ actF act a ] f) → x ⊨ ⟨ actF act a ⟩ ~ f
  ~[a]φ→⟨a⟩~φ _ _ _ h = h

  ⟨a⟩~φ→~[a]φ : (x : Program C α) → (a : Shape C) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF act a ⟩ ~ f → x ⊨ ~ ([ actF act a ] f)
  ⟨a⟩~φ→~[a]φ _ _ _ h = h

[a]true⇔true : (x : Program C α) → (a : Shape C) → x ⊨ [ actF act a ] true {ℓ = ℓ} ⇔ x ⊨ true {ℓ = ℓ}
[a]true⇔true x a = [a]true→true x a , true→[a]true x a
  where
  [a]true→true : (x : Program C α) → (a : Shape C) → x ⊨ [ actF act a ] true {ℓ = ℓ} → x ⊨ true {ℓ = ℓ}
  [a]true→true _ _ _ = tt

  true→[a]true : (x : Program C α) → (a : Shape C) → x ⊨ true {ℓ = ℓ} → x ⊨ [ actF act a ] true {ℓ = ℓ}
  true→[a]true x _ _ with free x
  ... | pure _ = tt
  ... | impure _ = λ _ _ → tt

[a]|φ∧ψ|⇔[a]φ∧[a]ψ : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ [ actF act a ] (f₁ ∧ f₂) ⇔ x ⊨ [ actF act a ] f₁ ∧ [ actF act a ] f₂
[a]|φ∧ψ|⇔[a]φ∧[a]ψ x a f₁ f₂ = [a]|φ∧ψ|→[a]φ∧[a]ψ x a f₁ f₂ , [a]φ∧[a]ψ→[a]|φ∧ψ| x a f₁ f₂
  where
  [a]|φ∧ψ|→[a]φ∧[a]ψ : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ [ actF act a ] (f₁ ∧ f₂) → x ⊨ [ actF act a ] f₁ ∧ [ actF act a ] f₂
  [a]|φ∧ψ|→[a]φ∧[a]ψ x _ _ _ h with free x
  ... | pure _ = tt , tt
  ... | impure _ = (λ { (lift refl) r → proj₁ (h (lift refl) r) }) , λ { (lift refl) r → proj₂ (h (lift refl) r) }

  [a]φ∧[a]ψ→[a]|φ∧ψ| : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ [ actF act a ] f₁ ∧ [ actF act a ] f₂ → x ⊨ [ actF act a ] (f₁ ∧ f₂)
  [a]φ∧[a]ψ→[a]|φ∧ψ| x _ _ _ (h₁ , h₂) with free x
  ... | pure _ = tt
  ... | impure _ = λ { (lift refl) r → h₁ (lift refl) r , h₂ (lift refl) r }

[a]|φ∨ψ|⇒⟨a⟩φ∨[a]ψ : (x : Program C α) → (a : Shape C) → (f₁ f₂ : Formula (Shape C) ℓ) → x ⊨ [ actF act a ] (f₁ ∨ f₂) → x ⊨ ⟨ actF act a ⟩ f₁ ∨ [ actF act a ] f₂
[a]|φ∨ψ|⇒⟨a⟩φ∨[a]ψ x a f₁ f₂ h with ⊨-dec x (⟨ actF act a ⟩ f₁)
... | yes h₁ = inj₁ h₁
... | no hn₁ with ⊨-dec x ([ actF act a ] f₂)
...   | yes h₂ = inj₂ h₂
...   | no hn₂ with free x
...     | pure _ = inj₂ tt
...     | impure _ = ⊥₀-elim (hn₂ λ { (lift refl) r → case h (lift refl) r of λ { (inj₁ h₁) → ⊥₀-elim (hn₁ (lift refl , r , h₁))
                                                                                ; (inj₂ h₂) → h₂ } })

-- Fixed point equations

-- μX．φ→νX．φ

-- Theorems for μ_．_

-- μX．X⇔false

-- μX．⟨R⟩X⇔false

-- Theorems for ν_．_

-- νX．X⇔true

-- νX．[R]X⇔true

-- RegularFormulas

-- Theorems for ⟨_⟩_

⟨ε⟩φ⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ ε ⟩ f ⇔ x ⊨ f
⟨ε⟩φ⇔φ x f = ⟨ε⟩φ→φ x f , φ→⟨ε⟩φ x f
  where
  ⟨ε⟩φ→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ ε ⟩ f → x ⊨ f
  ⟨ε⟩φ→φ _ _ h = h

  φ→⟨ε⟩φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ ⟨ ε ⟩ f
  φ→⟨ε⟩φ _ _ h = h

⟨false⟩φ⇔false : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF false ⟩ f ⇔ x ⊨ false {ℓ = ℓ}
⟨false⟩φ⇔false x f = ⟨false⟩φ→false x f , false→⟨false⟩φ x f
  where
  ⟨false⟩φ→false : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF false ⟩ f → x ⊨ false {ℓ = ℓ}
  ⟨false⟩φ→false x _ h with free x
  ⟨false⟩φ→false x _ () | pure _
  ⟨false⟩φ→false x _ () | impure _

  false→⟨false⟩φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ false {ℓ = ℓ} → x ⊨ ⟨ actF false ⟩ f
  false→⟨false⟩φ _ _ ()

⟨af₁∪af₂⟩φ⇔⟨af₁⟩φ∨⟨af₂⟩φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF af₁ ∪ af₂ ⟩ f ⇔ x ⊨ ⟨ actF af₁ ⟩ f ∨ ⟨ actF af₂ ⟩ f
⟨af₁∪af₂⟩φ⇔⟨af₁⟩φ∨⟨af₂⟩φ x af₁ af₂ f = ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ x af₁ af₂ f , ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ x af₁ af₂ f
  where
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF af₁ ∪ af₂ ⟩ f → x ⊨ ⟨ actF af₁ ⟩ f ∨ ⟨ actF af₂ ⟩ f
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ x _ _ _ h with free x
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ x _ _ _ (inj₁ h∈₁ , r , h) | impure _ = inj₁ (h∈₁ , r , h)
  ⟨af₁∪af₂⟩φ→⟨af₁⟩φ∨⟨af₂⟩φ x _ _ _ (inj₂ h∈₂ , r , h) | impure _ = inj₂ (h∈₂ , r , h)

  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF af₁ ⟩ f ∨ ⟨ actF af₂ ⟩ f → x ⊨ ⟨ actF af₁ ∪ af₂ ⟩ f
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ x _ _ _ h with free x
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ x _ _ _ (inj₁ ()) | pure _
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ x _ _ _ (inj₂ ()) | pure _
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ x _ _ _ (inj₁ (h∈₁ , r , h)) | impure _ = inj₁ h∈₁ , r , h
  ⟨af₁⟩φ∨⟨af₂⟩φ→⟨af₁∪af₂⟩φ x _ _ _ (inj₂ (h∈₂ , r , h)) | impure _ = inj₂ h∈₂ , r , h

⟨af₁∩af₂⟩φ→⟨af₁⟩φ∧⟨af₂⟩φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF af₁ ∩ af₂ ⟩ f → x ⊨ ⟨ actF af₁ ⟩ f ∧ ⟨ actF af₂ ⟩ f
⟨af₁∩af₂⟩φ→⟨af₁⟩φ∧⟨af₂⟩φ x _ _ _ h with free x
⟨af₁∩af₂⟩φ→⟨af₁⟩φ∧⟨af₂⟩φ x _ _ _ ((h∈₁ , h∈₂) , r , h) | impure _ = (h∈₁ , r , h) , h∈₂ , r , h

⟨∃d:D．AF|d|⟩φ⇔∃d:D．⟨AF|d|⟩φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF ∃ᵃᶠ⦗ D ⦘ (λ d → af d) ⟩ f ⇔ x ⊨ ∃ᶠ⦗ D ⦘ λ d → ⟨ actF af d ⟩ f
⟨∃d:D．AF|d|⟩φ⇔∃d:D．⟨AF|d|⟩φ x D af f = ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ x D af f , ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ x D af f
  where
  ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF ∃ᵃᶠ⦗ D ⦘ (λ d → af d) ⟩ f → x ⊨ ∃ᶠ⦗ D ⦘ λ d → ⟨ actF af d ⟩ f
  ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ x _ _ _ h with free x
  ⟨∃d:D．AF|d|⟩φ→∃d:D．⟨AF|d|⟩φ x _ _ _ ((d , h∈) , r , h) | impure _ = d , h∈ , r , h

  ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → ⟨ actF af d ⟩ f) → x ⊨ ⟨ actF ∃ᵃᶠ⦗ D ⦘ (λ d → af d) ⟩ f
  ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ x _ _ _ h with free x
  ∃d:D．⟨AF|d|⟩φ→⟨∃d:D．AF|d|⟩φ x _ _ _ (d , h∈ , r , h) | impure _ = (d , h∈) , r , h

⟨∀d:D．AF|d|⟩φ→∀d:D．⟨AF|d|⟩φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ actF ∀ᵃᶠ⦗ D ⦘ (λ d → af d) ⟩ f → x ⊨ ∀ᶠ⦗ D ⦘ λ d → ⟨ actF af d ⟩ f
⟨∀d:D．AF|d|⟩φ→∀d:D．⟨AF|d|⟩φ x _ _ _ h d with free x
⟨∀d:D．AF|d|⟩φ→∀d:D．⟨AF|d|⟩φ x _ _ _ (h∈ , r , h) d | impure _ = h∈ d , r , h

⟨R₁+R₂⟩φ⇔⟨R₁⟩φ∨⟨R₂⟩φ : (x : Program C α) → (R₁ R₂ : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ R₁ + R₂ ⟩ f ⇔ x ⊨ ⟨ R₁ ⟩ f ∨ ⟨ R₂ ⟩ f
⟨R₁+R₂⟩φ⇔⟨R₁⟩φ∨⟨R₂⟩φ x R₁ R₂ f = ⟨R₁+R₂⟩φ→⟨R₁⟩φ∨⟨R₂⟩φ x R₁ R₂ f , ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ x R₁ R₂ f
  where
  ⟨R₁+R₂⟩φ→⟨R₁⟩φ∨⟨R₂⟩φ : (x : Program C α) → (R₁ R₂ : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ R₁ + R₂ ⟩ f → x ⊨ ⟨ R₁ ⟩ f ∨ ⟨ R₂ ⟩ f
  ⟨R₁+R₂⟩φ→⟨R₁⟩φ∨⟨R₂⟩φ _ _ _ _ h = h

  ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ : (x : Program C α) → (R₁ R₂ : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ R₁ ⟩ f ∨ ⟨ R₂ ⟩ f → x ⊨ ⟨ R₁ + R₂ ⟩ f
  ⟨R₁⟩φ∨⟨R₂⟩φ→⟨R₁+R₂⟩φ _ _ _ _ h = h

-- ⟨R₁·R₂⟩φ⇔⟨R₁⟩⟨R₂⟩φ

-- ⟨R*⟩φ⇔μX．|⟨R⟩X∨φ|

-- ⟨R⁺⟩φ⇔⟨R⟩⟨R*⟩φ

~⟨R⟩φ⇔[R]~φ : (x : Program C α) → (R : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ~ (⟨ R ⟩ f) ⇔ x ⊨ [ R ] ~ f
~⟨R⟩φ⇔[R]~φ x R f = ~⟨R⟩φ→[R]~φ x R f , [R]~φ→~⟨R⟩φ x R f
  where
  ~⟨R⟩φ→[R]~φ : (x : Program C α) → (R : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ~ (⟨ R ⟩ f) → x ⊨ [ R ] ~ f
  ~⟨R⟩φ→[R]~φ _ _ _ h = h

  [R]~φ→~⟨R⟩φ : (x : Program C α) → (R : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ R ] ~ f → x ⊨ ~ (⟨ R ⟩ f)
  [R]~φ→~⟨R⟩φ _ _ _ h = h

-- ⟨R⟩false⇔false

-- ⟨R⟩|φ∨ψ|⇔⟨R⟩φ∨⟨R⟩ψ

-- ⟨R⟩φ∧[R]ψ→⟨R⟩|φ∧ψ|

-- Theorems for [_]_

[ε]φ⇔φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ [ ε ] f ⇔ x ⊨ f
[ε]φ⇔φ x f = [ε]φ→φ x f , φ→[ε]φ x f
  where
  [ε]φ→φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ [ ε ] f → x ⊨ f
  [ε]φ→φ _ _ h = h

  φ→[ε]φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ f → x ⊨ [ ε ] f
  φ→[ε]φ _ _ h = h

[false]φ⇔true : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF false ] f ⇔ x ⊨ true {ℓ = ℓ}
[false]φ⇔true x f = [false]φ→true x f , true→[false]φ x f
  where
  [false]φ→true : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF false ] f → x ⊨ true {ℓ = ℓ}
  [false]φ→true _ _ _ = tt

  true→[false]φ : (x : Program C α) → (f : Formula (Shape C) ℓ) → x ⊨ true {ℓ = ℓ} → x ⊨ [ actF false ] f
  true→[false]φ x _ _ with free x
  ... | pure _ = tt
  ... | impure _ = λ ()

[af₁∪af₂]φ⇔[af₁]φ∧[af₁]φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF af₁ ∪ af₂ ] f ⇔ x ⊨ [ actF af₁ ] f ∧ [ actF af₂ ] f
[af₁∪af₂]φ⇔[af₁]φ∧[af₁]φ x af₁ af₂ f = [af₁∪af₂]φ→[af₁]φ∧[af₁]φ x af₁ af₂ f , [af₁]φ∧[af₁]φ→[af₁∪af₂]φ x af₁ af₂ f
  where
  [af₁∪af₂]φ→[af₁]φ∧[af₁]φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF af₁ ∪ af₂ ] f → x ⊨ [ actF af₁ ] f ∧ [ actF af₂ ] f
  [af₁∪af₂]φ→[af₁]φ∧[af₁]φ x _ _ _ h with free x
  ... | pure _ = tt , tt
  ... | impure _ = (λ h∈₁ r → h (inj₁ h∈₁) r) , λ h∈₂ r → h (inj₂ h∈₂) r

  [af₁]φ∧[af₁]φ→[af₁∪af₂]φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF af₁ ] f ∧ [ actF af₂ ] f → x ⊨ [ actF af₁ ∪ af₂ ] f
  [af₁]φ∧[af₁]φ→[af₁∪af₂]φ x _ _ _ (h₁ , h₂) with free x
  ... | pure _ = tt
  ... | impure _ = λ { (inj₁ h∈₁) r → h₁ h∈₁ r
                     ; (inj₂ h∈₂) r → h₂ h∈₂ r }

[af₁]φ∨[af₂]φ→[af₁∩af₂]φ : (x : Program C α) → (af₁ af₂ : ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF af₁ ] f ∨ [ actF af₂ ] f → x ⊨ [ actF af₁ ∩ af₂ ] f
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ x _ _ _ h with free x
... | pure _ = tt
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ x _ _ _ (inj₁ h₁) | impure _ = λ { (h∈₁ , _) r → h₁ h∈₁ r }
[af₁]φ∨[af₂]φ→[af₁∩af₂]φ x _ _ _ (inj₂ h₂) | impure _ = λ { (_ , h∈₂) r → h₂ h∈₂ r }

[∃d:D．AF|d|]φ⇔∀d:D．[AF|d|]φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF ∃ᵃᶠ⦗ D ⦘ (λ d → af d) ] f ⇔ x ⊨ ∀ᶠ⦗ D ⦘ λ d → [ actF af d ] f
[∃d:D．AF|d|]φ⇔∀d:D．[AF|d|]φ x D af f = [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ x D af f , ∀d:D．[AF|d|]φ→[∃d:D．AF|d|]φ x D af f
  where
  [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ actF ∃ᵃᶠ⦗ D ⦘ (λ d → af d) ] f → x ⊨ ∀ᶠ⦗ D ⦘ λ d → [ actF af d ] f
  [∃d:D．AF|d|]φ→∀d:D．[AF|d|]φ x _ _ _ h d with free x
  ... | pure _ = tt
  ... | impure _ = λ h∈ r → h (d , h∈) r

  ∀d:D．[AF|d|]φ→[∃d:D．AF|d|]φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ∀ᶠ⦗ D ⦘ (λ d → [ actF af d ] f) → x ⊨ [ actF ∃ᵃᶠ⦗ D ⦘ (λ d → af d) ] f
  ∀d:D．[AF|d|]φ→[∃d:D．AF|d|]φ x _ _ _ h with free x
  ... | pure _ = tt
  ... | impure _ = λ { (d , h∈) r → h d h∈ r }

∃d:D．[AF|d|]φ→[∀d:D．AF|d|]φ : (x : Program C α) → (D : Set ℓ) → (af : D → ActionFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ∃ᶠ⦗ D ⦘ (λ d → [ actF af d ] f) → x ⊨ [ actF ∀ᵃᶠ⦗ D ⦘ (λ d → af d) ] f
∃d:D．[AF|d|]φ→[∀d:D．AF|d|]φ x _ _ _ h with free x
... | pure _ = tt
∃d:D．[AF|d|]φ→[∀d:D．AF|d|]φ x _ _ _ (d , h) | impure _ = λ h∈ r → h (h∈ d) r

[R₁+R₂]φ⇔[R₁]φ∧[R₂]φ : (x : Program C α) → (R₁ R₂ : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ R₁ + R₂ ] f ⇔ x ⊨ [ R₁ ] f ∧ [ R₂ ] f
[R₁+R₂]φ⇔[R₁]φ∧[R₂]φ x R₁ R₂ f = [R₁+R₂]φ→[R₁]φ∧[R₂]φ x R₁ R₂ f , [R₁]φ∧[R₂]φ→[R₁+R₂]φ x R₁ R₂ f
  where
  [R₁+R₂]φ→[R₁]φ∧[R₂]φ : (x : Program C α) → (R₁ R₂ : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ R₁ + R₂ ] f → x ⊨ [ R₁ ] f ∧ [ R₂ ] f
  [R₁+R₂]φ→[R₁]φ∧[R₂]φ _ _ _ _ h = h

  [R₁]φ∧[R₂]φ→[R₁+R₂]φ : (x : Program C α) → (R₁ R₂ : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ [ R₁ ] f ∧ [ R₂ ] f → x ⊨ [ R₁ + R₂ ] f
  [R₁]φ∧[R₂]φ→[R₁+R₂]φ _ _ _ _ h = h

-- [R₁·R₂]φ⇔[R₁][R₂]φ

-- [R*]φ⇔νX．|[R]X∧φ|

-- [R⁺]φ⇔[R][R*]φ

~[R]φ⇔⟨R⟩~φ : (x : Program C α) → (R : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ~ ([ R ] f) ⇔ x ⊨ ⟨ R ⟩ ~ f
~[R]φ⇔⟨R⟩~φ x R f = ~[R]φ→⟨R⟩~φ x R f , ⟨R⟩~φ→~[R]φ x R f
  where
  ~[R]φ→⟨R⟩~φ : (x : Program C α) → (R : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ~ ([ R ] f) → x ⊨ ⟨ R ⟩ ~ f
  ~[R]φ→⟨R⟩~φ _ _ _ h = h

  ⟨R⟩~φ→~[R]φ : (x : Program C α) → (R : RegularFormula (Shape C) ℓ) → (f : Formula (Shape C) ℓ) → x ⊨ ⟨ R ⟩ ~ f → x ⊨ ~ ([ R ] f)
  ⟨R⟩~φ→~[R]φ _ _ _ h = h

-- [R]true⇔true

-- [R]|φ∧ψ|⇔[R]φ∧[R]ψ

-- [R]|φ∨ψ|→⟨R⟩φ∨[R]ψ
