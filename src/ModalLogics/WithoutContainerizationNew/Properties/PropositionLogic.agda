{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.PropositionLogic where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container; Shape)
open import Data.List using (List; map)
open import Data.Product using (_,_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (Context; Formulaⁱ; _⊢_⊨'_; _⊢_⊨ⁱ_)

open Formulaⁱ
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))
  flags : List Bool

-- Theorems for ~_

~true⇔false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → _⊢_⊨ⁱ_ {flags = flags} Γ x (~ true) ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x false
~true⇔false {flags = flags} Γ x = ~true→false {flags = flags} Γ x , false→~true {flags = flags} Γ x
  where
  ~true→false : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → _⊢_⊨ⁱ_ {flags = flags} Γ x (~ true) → _⊢_⊨ⁱ_ {flags = flags} Γ x false
  ~true→false _ _ ()

  false→~true : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → _⊢_⊨ⁱ_ {flags = flags} Γ x false → _⊢_⊨ⁱ_ {flags = flags} Γ x (~ true)
  false→~true _ _ ()

~false⇔true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → _⊢_⊨ⁱ_ {flags = flags} Γ x (~ false) ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x true
~false⇔true {flags = flags} Γ x = ~false→true {flags = flags} Γ x , true→~false {flags = flags} Γ x
  where
  ~false→true : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → _⊢_⊨ⁱ_ {flags = flags} Γ x (~ false) → _⊢_⊨ⁱ_ {flags = flags} Γ x true
  ~false→true _ _ _ = `true

  true→~false : {flags : List Bool} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → _⊢_⊨ⁱ_ {flags = flags} Γ x true → _⊢_⊨ⁱ_ {flags = flags} Γ x (~ false)
  true→~false _ _ _ = `true

~|φ∧ψ|⇔|~φ|∨|~ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (fⁱ₁ ∧ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∨ (~ fⁱ₂)
~|φ∧ψ|⇔|~φ|∨|~ψ| Γ x fⁱ₁ fⁱ₂ = ~|φ∧ψ|→|~φ|∨|~ψ| Γ x fⁱ₁ fⁱ₂ , |~φ|∨|~ψ|→~|φ∧ψ| Γ x fⁱ₁ fⁱ₂
  where
  ~|φ∧ψ|→|~φ|∨|~ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (fⁱ₁ ∧ fⁱ₂) → Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∨ (~ fⁱ₂)
  ~|φ∧ψ|→|~φ|∨|~ψ| _ _ _ _ h = h

  |~φ|∨|~ψ|→~|φ∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∨ (~ fⁱ₂) → Γ ⊢ x ⊨ⁱ ~ (fⁱ₁ ∧ fⁱ₂)
  |~φ|∨|~ψ|→~|φ∧ψ| _ _ _ _ h = h

~|φ∨ψ|⇔|~φ|∧|~ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (fⁱ₁ ∨ fⁱ₂) ⇔ Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∧ (~ fⁱ₂)
~|φ∨ψ|⇔|~φ|∧|~ψ| Γ x fⁱ₁ fⁱ₂ = ~|φ∨ψ|→|~φ|∧|~ψ| Γ x fⁱ₁ fⁱ₂ , |~φ|∧|~ψ|→~|φ∨ψ| Γ x fⁱ₁ fⁱ₂
  where
  ~|φ∨ψ|→|~φ|∧|~ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ ~ (fⁱ₁ ∨ fⁱ₂) → Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∧ (~ fⁱ₂)
  ~|φ∨ψ|→|~φ|∧|~ψ| _ _ _ _ h = h

  |~φ|∧|~ψ|→~|φ∨ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∧ (~ fⁱ₂) → Γ ⊢ x ⊨ⁱ ~ (fⁱ₁ ∨ fⁱ₂)
  |~φ|∧|~ψ|→~|φ∨ψ| _ _ _ _ h = h

~~φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not (map not flags))) → Γ ⊢ x ⊨ⁱ ~ ~ fⁱ ⇔ Γ ⊢ x ⊨ⁱ fⁱ
~~φ⇔φ Γ x fⁱ = ~~φ→φ Γ x fⁱ , φ→~~φ Γ x fⁱ
  where
  ~~φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not (map not flags))) → Γ ⊢ x ⊨ⁱ ~ ~ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ
  ~~φ→φ _ _ _ h = h

  φ→~~φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev (map not (map not flags))) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ ~ ~ fⁱ
  φ→~~φ _ _ _ h = h

-- Theorems for _∧_

φ∧true⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∧ true ⇔ Γ ⊢ x ⊨ⁱ fⁱ
φ∧true⇔φ Γ x fⁱ = φ∧true→φ Γ x fⁱ , φ→φ∧true Γ x fⁱ
  where
  φ∧true→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∧ true → Γ ⊢ x ⊨ⁱ fⁱ
  φ∧true→φ _ _ _ (h , _) = h

  φ→φ∧true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ ∧ true
  φ→φ∧true _ _ _ h = h , `true

φ∧false⇔false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∧ false ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x false
φ∧false⇔false Γ x fⁱ = φ∧false→false Γ x fⁱ , false→φ∧false Γ x fⁱ
  where
  φ∧false→false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∧ false → _⊢_⊨ⁱ_ {flags = flags} Γ x false
  φ∧false→false _ _ _ (_ , ())

  false→φ∧false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → _⊢_⊨ⁱ_ {flags = flags} Γ x false → Γ ⊢ x ⊨ⁱ fⁱ ∧ false
  false→φ∧false _ _ _ ()

φ∧φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∧ fⁱ ⇔ Γ ⊢ x ⊨ⁱ fⁱ
φ∧φ⇔φ Γ x fⁱ = φ∧φ→φ Γ x fⁱ , φ→φ∧φ Γ x fⁱ
  where
  φ∧φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∧ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ
  φ∧φ→φ _ _ _ (h , _) = h

  φ→φ∧φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ ∧ fⁱ
  φ→φ∧φ _ _ _ h = h , h

φ∧ψ⇔ψ∧φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ fⁱ₂ ⇔ Γ ⊢ x ⊨ⁱ fⁱ₂ ∧ fⁱ₁
φ∧ψ⇔ψ∧φ Γ x fⁱ₁ fⁱ₂ = ∧-comm Γ x fⁱ₁ fⁱ₂ , ∧-comm Γ x fⁱ₂ fⁱ₁
  where
  ∧-comm : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ fⁱ₂ → Γ ⊢ x ⊨ⁱ fⁱ₂ ∧ fⁱ₁
  ∧-comm _ _ _ _ (h₁ , h₂) = h₂ , h₁

|φ∧ψ|∧χ⇔φ∧|ψ∧χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∧ fⁱ₂) ∧ fⁱ₃ ⇔ Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ (fⁱ₂ ∧ fⁱ₃)
|φ∧ψ|∧χ⇔φ∧|ψ∧χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ = |φ∧ψ|∧χ→φ∧|ψ∧χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ , φ∧|ψ∧χ|→|φ∧ψ|∧χ Γ x fⁱ₁ fⁱ₂ fⁱ₃
  where
  |φ∧ψ|∧χ→φ∧|ψ∧χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∧ fⁱ₂) ∧ fⁱ₃ → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ (fⁱ₂ ∧ fⁱ₃)
  |φ∧ψ|∧χ→φ∧|ψ∧χ| _ _ _ _ _ ((h₁ , h₂) , h₃) = h₁ , (h₂ , h₃)

  φ∧|ψ∧χ|→|φ∧ψ|∧χ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ (fⁱ₂ ∧ fⁱ₃) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∧ fⁱ₂) ∧ fⁱ₃
  φ∧|ψ∧χ|→|φ∧ψ|∧χ _ _ _ _ _ (h₁ , (h₂ , h₃)) = (h₁ , h₂) , h₃

φ∧|ψ∨χ|⇔|φ∧ψ|∨|φ∧χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ (fⁱ₂ ∨ fⁱ₃) ⇔ Γ ⊢ x ⊨ⁱ (fⁱ₁ ∧ fⁱ₂) ∨ (fⁱ₁ ∧ fⁱ₃)
φ∧|ψ∨χ|⇔|φ∧ψ|∨|φ∧χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ = φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ , |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃
  where
  φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ (fⁱ₂ ∨ fⁱ₃) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∧ fⁱ₂) ∨ (fⁱ₁ ∧ fⁱ₃)
  φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| _ _ _ _ _ (h₁ , inj₁ h₂) = inj₁ (h₁ , h₂)
  φ∧|ψ∨χ|→|φ∧ψ|∨|φ∧χ| _ _ _ _ _ (h₁ , inj₂ h₃) = inj₂ (h₁ , h₃)

  |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∧ fⁱ₂) ∨ (fⁱ₁ ∧ fⁱ₃) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∧ (fⁱ₂ ∨ fⁱ₃)
  |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| _ _ _ _ _ (inj₁ (h₁ , h₂)) = h₁ , inj₁ h₂
  |φ∧ψ|∨|φ∧χ|→φ∧|ψ∨χ| _ _ _ _ _ (inj₂ (h₁ , h₃)) = h₁ , inj₂ h₃

-- Theorems for _∨_

φ∨true⇔true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∨ true ⇔ _⊢_⊨ⁱ_ {flags = flags} Γ x true
φ∨true⇔true Γ x fⁱ = φ∨true→true Γ x fⁱ , true→φ∨true Γ x fⁱ
  where
  φ∨true→true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∨ true → _⊢_⊨ⁱ_ {flags = flags} Γ x true
  φ∨true→true _ _ _ _ = `true

  true→φ∨true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → _⊢_⊨ⁱ_ {flags = flags} Γ x true → Γ ⊢ x ⊨ⁱ fⁱ ∨ true
  true→φ∨true _ _ _ _ = inj₂ `true

φ∨false⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∨ false ⇔ Γ ⊢ x ⊨ⁱ fⁱ
φ∨false⇔φ Γ x fⁱ = φ∨false→φ Γ x fⁱ , φ→φ∨false Γ x fⁱ
  where
  φ∨false→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∨ false → Γ ⊢ x ⊨ⁱ fⁱ
  φ∨false→φ _ _ _ (inj₁ h) = h

  φ→φ∨false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ ∨ false
  φ→φ∨false _ _ _ h = inj₁ h

φ∨φ⇔φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∨ fⁱ ⇔ Γ ⊢ x ⊨ⁱ fⁱ
φ∨φ⇔φ Γ x fⁱ = φ∨φ→φ Γ x fⁱ , φ→φ∨φ Γ x fⁱ
  where
  φ∨φ→φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ ∨ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ
  φ∨φ→φ _ _ _ (inj₁ h) = h
  φ∨φ→φ _ _ _ (inj₂ h) = h

  φ→φ∨φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ → Γ ⊢ x ⊨ⁱ fⁱ ∨ fⁱ
  φ→φ∨φ _ _ _ h = inj₁ h

φ∨ψ⇔ψ∨φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ fⁱ₂ ⇔ Γ ⊢ x ⊨ⁱ fⁱ₂ ∨ fⁱ₁
φ∨ψ⇔ψ∨φ Γ x fⁱ₁ fⁱ₂ = ∨-comm Γ x fⁱ₁ fⁱ₂ , ∨-comm Γ x fⁱ₂ fⁱ₁
  where
  ∨-comm : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ fⁱ₂ → Γ ⊢ x ⊨ⁱ fⁱ₂ ∨ fⁱ₁
  ∨-comm _ _ _ _ (inj₁ h₁) = inj₂ h₁
  ∨-comm _ _ _ _ (inj₂ h₂) = inj₁ h₂

|φ∨ψ|∨χ⇔φ∨|ψ∨χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∨ fⁱ₂) ∨ fⁱ₃ ⇔ Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ (fⁱ₂ ∨ fⁱ₃)
|φ∨ψ|∨χ⇔φ∨|ψ∨χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ = |φ∨ψ|∨χ→φ∨|ψ∨χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ , φ∨|ψ∨χ|→|φ∨ψ|∨χ Γ x fⁱ₁ fⁱ₂ fⁱ₃
  where
  |φ∨ψ|∨χ→φ∨|ψ∨χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∨ fⁱ₂) ∨ fⁱ₃ → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ (fⁱ₂ ∨ fⁱ₃)
  |φ∨ψ|∨χ→φ∨|ψ∨χ| _ _ _ _ _ (inj₁ (inj₁ h₁)) = inj₁ h₁
  |φ∨ψ|∨χ→φ∨|ψ∨χ| _ _ _ _ _ (inj₁ (inj₂ h₂)) = inj₂ (inj₁ h₂)
  |φ∨ψ|∨χ→φ∨|ψ∨χ| _ _ _ _ _ (inj₂ h₃) = inj₂ (inj₂ h₃)

  φ∨|ψ∨χ|→|φ∨ψ|∨χ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ (fⁱ₂ ∨ fⁱ₃) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∨ fⁱ₂) ∨ fⁱ₃
  φ∨|ψ∨χ|→|φ∨ψ|∨χ _ _ _ _ _ (inj₁ h₁) = inj₁ (inj₁ h₁)
  φ∨|ψ∨χ|→|φ∨ψ|∨χ _ _ _ _ _ (inj₂ (inj₁ h₂)) = inj₁ (inj₂ h₂)
  φ∨|ψ∨χ|→|φ∨ψ|∨χ _ _ _ _ _ (inj₂ (inj₂ h₃)) = inj₂ h₃

φ∨|ψ∧χ|⇔|φ∨ψ|∧|φ∨χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ (fⁱ₂ ∧ fⁱ₃) ⇔ Γ ⊢ x ⊨ⁱ (fⁱ₁ ∨ fⁱ₂) ∧ (fⁱ₁ ∨ fⁱ₃)
φ∨|ψ∧χ|⇔|φ∨ψ|∧|φ∨χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ = φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃ , |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| Γ x fⁱ₁ fⁱ₂ fⁱ₃
  where
  φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ (fⁱ₂ ∧ fⁱ₃) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∨ fⁱ₂) ∧ (fⁱ₁ ∨ fⁱ₃)
  φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| _ _ _ _ _ (inj₁ h₁) = inj₁ h₁ , inj₁ h₁
  φ∨|ψ∧χ|→|φ∨ψ|∧|φ∨χ| _ _ _ _ _ (inj₂ (h₂ , h₃)) = inj₂ h₂ , inj₂ h₃

  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ fⁱ₂ fⁱ₃ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (fⁱ₁ ∨ fⁱ₂) ∧ (fⁱ₁ ∨ fⁱ₃) → Γ ⊢ x ⊨ⁱ fⁱ₁ ∨ (fⁱ₂ ∧ fⁱ₃)
  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| _ _ _ _ _ (inj₁ h₁ , _) = inj₁ h₁
  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| _ _ _ _ _ (_ , inj₁ h₁) = inj₁ h₁
  |φ∨ψ|∧|φ∨χ|→φ∨|ψ∧χ| _ _ _ _ _ (inj₂ h₂ , inj₂ h₃) = inj₂ (h₂ , h₃)

-- Theorems for _⇒_

φ⇒ψ⇔|~φ|∨ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ⇒ fⁱ₂ ⇔ Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∨ fⁱ₂
φ⇒ψ⇔|~φ|∨ψ Γ x fⁱ₁ fⁱ₂ = φ⇒ψ→|~φ|∨ψ Γ x fⁱ₁ fⁱ₂ , |~φ|∨ψ→φ⇒ψ Γ x fⁱ₁ fⁱ₂
  where
  φ⇒ψ→|~φ|∨ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ fⁱ₁ ⇒ fⁱ₂ → Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∨ fⁱ₂
  φ⇒ψ→|~φ|∨ψ _ _ _ _ h = h

  |~φ|∨ψ→φ⇒ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (fⁱ₁ : Formulaⁱ (Shape C) ℓ prev (map not flags)) → (fⁱ₂ : Formulaⁱ (Shape C) ℓ prev flags) → Γ ⊢ x ⊨ⁱ (~ fⁱ₁) ∨ fⁱ₂ → Γ ⊢ x ⊨ⁱ fⁱ₁ ⇒ fⁱ₂
  |~φ|∨ψ→φ⇒ψ _ _ _ _ h = h
