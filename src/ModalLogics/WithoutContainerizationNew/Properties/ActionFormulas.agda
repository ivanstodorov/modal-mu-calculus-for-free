{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.ActionFormulas where

open import Common.Biconditional using (_⇔_)
open import Common.RegularFormulasWithData using (ActionFormula; _∈_)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import Level using (Level)

open ActionFormula

private variable
  a ℓ : Level
  α : Set a

trueᶜ⇔false : (a : α) → _∈_ {ℓ = ℓ} a (true ᶜ) ⇔ _∈_ {ℓ = ℓ} a false
trueᶜ⇔false {ℓ = ℓ} a = trueᶜ→false {ℓ = ℓ} a , false→trueᶜ {ℓ = ℓ} a
  where
  trueᶜ→false : {ℓ : Level} → (a : α) → _∈_ {ℓ = ℓ} a (true ᶜ) → _∈_ {ℓ = ℓ} a false
  trueᶜ→false _ h = ⊥₀-elim (h tt)

  false→trueᶜ : {ℓ : Level} → (a : α) → _∈_ {ℓ = ℓ} a false → _∈_ {ℓ = ℓ} a (true ᶜ)
  false→trueᶜ _ ()

falseᶜ⇔true : (a : α) → _∈_ {ℓ = ℓ} a (false ᶜ) ⇔ _∈_ {ℓ = ℓ} a true
falseᶜ⇔true {ℓ = ℓ} a = falseᶜ→true {ℓ = ℓ} a , true→falseᶜ {ℓ = ℓ} a
  where
  falseᶜ→true : {ℓ : Level} → (a : α) → _∈_ {ℓ = ℓ} a (false ᶜ) → _∈_ {ℓ = ℓ} a true
  falseᶜ→true _ _ = tt

  true→falseᶜ : {ℓ : Level} → (a : α) → _∈_ {ℓ = ℓ} a true → _∈_ {ℓ = ℓ} a (false ᶜ)
  true→falseᶜ _ _ ()

|∃d:D．A|d||ᶜ⇔∀d:D．|A|d||ᶜ : (a : α) → (D : Set ℓ) → (af : D → ActionFormula α ℓ) → a ∈ (∃⦗ D ⦘ λ d → af d) ᶜ ⇔ a ∈ ∀⦗ D ⦘ λ d → (af d) ᶜ
|∃d:D．A|d||ᶜ⇔∀d:D．|A|d||ᶜ a D af = |∃d:D．A|d||ᶜ→∀d:D．|A|d||ᶜ a D af , ∀d:D．|A|d||ᶜ→|∃d:D．A|d||ᶜ a D af
  where
  |∃d:D．A|d||ᶜ→∀d:D．|A|d||ᶜ : (a : α) → (D : Set ℓ) → (af : D → ActionFormula α ℓ) → a ∈ (∃⦗ D ⦘ λ d → af d) ᶜ → a ∈ ∀⦗ D ⦘ λ d → (af d) ᶜ
  |∃d:D．A|d||ᶜ→∀d:D．|A|d||ᶜ _ _ _ hn∃ d h = hn∃ (d , h)

  ∀d:D．|A|d||ᶜ→|∃d:D．A|d||ᶜ : (a : α) → (D : Set ℓ) → (af : D → ActionFormula α ℓ) → a ∈ ∀⦗ D ⦘ (λ d → (af d) ᶜ) → a ∈ (∃⦗ D ⦘ λ d → af d) ᶜ
  ∀d:D．|A|d||ᶜ→|∃d:D．A|d||ᶜ _ _ _ h∀ (d , h) = (h∀ d) h
