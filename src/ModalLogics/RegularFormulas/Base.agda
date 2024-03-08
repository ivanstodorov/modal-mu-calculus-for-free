{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.RegularFormulas.Base where

open import Common.ActionFormulas using (ActionFormula)
open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Level using (Level; _⊔_)
open import ModalLogics.FixedPoints.Base using () renaming (Formula to Formulaᶠᵖ; _⊩_ to _⊩ᶠᵖ_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)

open ℕ
open Formulaᶠᵖ

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 55 actF
infix 50 _*
infix 50 _⁺
infixr 45 _·_
infixr 45 _+_

data RegularFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  ε : RegularFormula C
  actF : ActionFormula C → RegularFormula C
  _·_ _+_ : RegularFormula C → RegularFormula C → RegularFormula C
  _* _⁺ : RegularFormula C → RegularFormula C

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ~_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : RegularFormula C → Formula C → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ⊩ x = f→fᶠᵖ f ⊩ᶠᵖ x
  where
  infix 55 actF
  infix 50 _*
  infixr 45 _·_
  infixr 45 _+_

  data RegularFormula' (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
    ε : RegularFormula' C
    actF : ActionFormula C → RegularFormula' C
    _·_ _+_ : RegularFormula' C → RegularFormula' C → RegularFormula' C
    _* : RegularFormula' C → RegularFormula' C

  rf→rf' : {C : Container ℓ₁ ℓ₂} → RegularFormula C → RegularFormula' C
  rf→rf' ε = ε
  rf→rf' (actF af) = actF af
  rf→rf' (rf₁ · rf₂) = rf→rf' rf₁ · rf→rf' rf₂
  rf→rf' (rf₁ + rf₂) = rf→rf' rf₁ + rf→rf' rf₂
  rf→rf' (rf *) = rf→rf' rf *
  rf→rf' (rf ⁺) = rf' · (rf' *)
    where
    rf' = rf→rf' rf

  f→fᶠᵖ : {C : Container ℓ₁ ℓ₂} → Formula C → Formulaᶠᵖ C
  f→fᶠᵖ true = true
  f→fᶠᵖ false = false
  f→fᶠᵖ (~ f) = ~ f→fᶠᵖ f
  f→fᶠᵖ (f₁ ∧ f₂) = f→fᶠᵖ f₁ ∧ f→fᶠᵖ f₂
  f→fᶠᵖ (f₁ ∨ f₂) = f→fᶠᵖ f₁ ∨ f→fᶠᵖ f₂
  f→fᶠᵖ (f₁ ⇒ f₂) = f→fᶠᵖ f₁ ⇒ f→fᶠᵖ f₂
  f→fᶠᵖ (⟨ rf ⟩ f) = helper-∃ (rf→rf' rf) (f→fᶠᵖ f) zero
    where
    helper-∃ : {C : Container ℓ₁ ℓ₂} → RegularFormula' C → Formulaᶠᵖ C → ℕ → Formulaᶠᵖ C
    helper-∃ ε fᶠᵖ _ = fᶠᵖ
    helper-∃ (actF af) fᶠᵖ _ = ⟨ af ⟩ fᶠᵖ
    helper-∃ (rf'₁ · rf'₂) fᶠᵖ i = helper-∃ rf'₁ (helper-∃ rf'₂ fᶠᵖ i) i
    helper-∃ (rf'₁ + rf'₂) fᶠᵖ i = helper-∃ rf'₁ fᶠᵖ i ∨ helper-∃ rf'₂ fᶠᵖ i
    helper-∃ (rf' *) fᶠᵖ i = μ show i ． helper-∃ rf' (var (show i)) (suc i) ∨ fᶠᵖ
  f→fᶠᵖ ([ rf ] f) = helper-∀ (rf→rf' rf) (f→fᶠᵖ f) zero
    where
    helper-∀ : {C : Container ℓ₁ ℓ₂} → RegularFormula' C → Formulaᶠᵖ C → ℕ → Formulaᶠᵖ C
    helper-∀ ε fᶠᵖ _ = fᶠᵖ
    helper-∀ (actF af) fᶠᵖ _ = [ af ] fᶠᵖ
    helper-∀ (rf'₁ · rf'₂) fᶠᵖ i = helper-∀ rf'₁ (helper-∀ rf'₂ fᶠᵖ i) i
    helper-∀ (rf'₁ + rf'₂) fᶠᵖ i = helper-∀ rf'₁ fᶠᵖ i ∨ helper-∀ rf'₂ fᶠᵖ i
    helper-∀ (rf' *) fᶠᵖ i = ν show i ． helper-∀ rf' (var (show i)) (suc i) ∧ fᶠᵖ

infix 25 _⊩_!_

_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C → Program C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
f ⊩ x ! i = f ⊩ (x i)

infix 25 _▸_⊩_!_

_▸_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula C → RecursiveProgram C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
n ▸ f ⊩ x ! i = f ⊩ (recursionHandler x n) i
