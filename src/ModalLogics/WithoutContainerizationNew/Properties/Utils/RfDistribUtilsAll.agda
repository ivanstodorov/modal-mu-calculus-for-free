{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.Utils.RfDistribUtilsAll where

open import Common.Program using (Program)
open import Data.Bool using (true)
open import Data.Container using (Container; Shape)
open import Data.Fin using (zero)
open import Data.List using (List)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (ActionNode; ActionTree; Arguments; Context; FixedPoint'; Formula'; Nu; _⊢_⊨'_; nuᶜ; at→af-∀)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.Utils using (Contextᵃᵗ; get-lift; _++-∀_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans)

open List
open ℕ
open _≤_
open ActionNode
open ActionTree
open Arguments
open Context
open Contextᵃᵗ
open FixedPoint'
open Formula'
open Nu
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))

[at]|φ∧ψ|→[at]φ∧[at]ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (f'₁ f'₂ : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∀ at (f'₁ ∧ f'₂) → Γ ⊢ x ⊨' at→af-∀ at f'₁ ∧ at→af-∀ at f'₂
[at]|φ∧ψ|→[at]φ∧[at]ψ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq , `[]-pure r h-eq
[at]|φ∧ψ|→[at]φ∧[at]ψ Γ _ ⦗ actF _ ⦘ f'₁ f'₂ (`[]-impure s c h-eq h) = `[]-impure s c h-eq (λ h∈ p → case h h∈ p of λ { (h , _) → h }) , `[]-impure s c h-eq (λ h∈ p → case h h∈ p of λ { (_ , h) → h })
[at]|φ∧ψ|→[at]φ∧[at]ψ {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ f'₁ f'₂ (`ν h) = `ν (helper₁' Γ x h) , `ν (helper₁'' Γ x h)
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift (f'₁ ∧ f'₂))

  fp'₂' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂' = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift f'₁)

  fp'₂'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂'' = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift f'₂)

  helper₁' : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp'₁ [] → Nu Γ x fp'₂' []
  nu (helper₁' Γ x h) = case nu h of λ { (h₁ , `lift (h₂ , _)) → helper₂ [] Γ x at zero z≤n h₁ , `lift h₂ }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁' Γ x h)
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , h₂ = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₂
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , (`lift h₂) = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₃ Γᵃᵗ Γ (c p) i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , `lift (helper₃ Γᵃᵗ Γ x i h≤ h₂)))
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₂ Γᵃᵗ Γ (c p) at i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at i h≤ h₁ , helper₃ Γᵃᵗ Γ x i h≤ h₂
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (h₁ , h₂) = helper₃ Γᵃᵗ Γ x i h≤ h₁ , helper₂ Γᵃᵗ Γ x at i h≤ h₂
    helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at₁ i h≤ h₁ , helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂

  helper₁'' : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp'₁ [] → Nu Γ x fp'₂'' []
  nu (helper₁'' Γ x h) = case nu h of λ { (h₁ , `lift (_ , h₂)) → helper₂ [] Γ x at zero z≤n h₁ , `lift h₂ }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁'' Γ x h)
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , h₂ = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₂
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , (`lift h₂) = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₃ Γᵃᵗ Γ (c p) i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , `lift (helper₃ Γᵃᵗ Γ x i h≤ h₂)))
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₂ Γᵃᵗ Γ (c p) at i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at i h≤ h₁ , helper₃ Γᵃᵗ Γ x i h≤ h₂
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (h₁ , h₂) = helper₃ Γᵃᵗ Γ x i h≤ h₁ , helper₂ Γᵃᵗ Γ x at i h≤ h₂
    helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at₁ i h≤ h₁ , helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂
[at]|φ∧ψ|→[at]φ∧[at]ψ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq , `[]-pure r h-eq
[at]|φ∧ψ|→[at]φ∧[at]ψ Γ _ ((actF _) · at) f'₁ f'₂ (`[]-impure s c h-eq h) = `[]-impure s c h-eq (λ h∈ p → case [at]|φ∧ψ|→[at]φ∧[at]ψ Γ (c p) at f'₁ f'₂ (h h∈ p) of λ { (h , _) → h }) , `[]-impure s c h-eq (λ h∈ p → case [at]|φ∧ψ|→[at]φ∧[at]ψ Γ (c p) at f'₁ f'₂ (h h∈ p) of λ { (_ , h) → h })
[at]|φ∧ψ|→[at]φ∧[at]ψ {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) f'₁ f'₂ (`ν h) = `ν (helper₁' Γ x h) , `ν (helper₁'' Γ x h)
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (f'₁ ∧ f'₂))

  fp'₂' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂' = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ f'₁)

  fp'₂'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂'' = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ f'₂)

  helper₁' : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp'₁ [] → Nu Γ x fp'₂' []
  nu (helper₁' Γ x h) = case nu h of λ { (h₁ , `lift h₂) → helper₂ [] Γ x at₁ zero z≤n h₁ , `lift (case [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at₂ f'₁ f'₂ h₂ of λ { (h , _) → h }) }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁' Γ x h)
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , h₂ = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₂
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , (`lift h₂) = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂') ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₃ Γᵃᵗ Γ (c p) i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , `lift (helper₃ Γᵃᵗ Γ x i h≤ h₂)))
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₂ Γᵃᵗ Γ (c p) at i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at i h≤ h₁ , helper₃ Γᵃᵗ Γ x i h≤ h₂
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (h₁ , h₂) = helper₃ Γᵃᵗ Γ x i h≤ h₁ , helper₂ Γᵃᵗ Γ x at i h≤ h₂
    helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at₁ i h≤ h₁ , helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂

  helper₁'' : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp'₁ [] → Nu Γ x fp'₂'' []
  nu (helper₁'' Γ x h) = case nu h of λ { (h₁ , `lift h₂) → helper₂ [] Γ x at₁ zero z≤n h₁ , `lift (case [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at₂ f'₁ f'₂ h₂ of λ { (_ , h) → h }) }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁'' Γ x h)
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , h₂ = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₂
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with nu h
    ... | h₁ , (`lift h₂) = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂'') ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₃ Γᵃᵗ Γ (c p) i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ , `lift (helper₃ Γᵃᵗ Γ x i h≤ h₂)))
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → helper₂ Γᵃᵗ Γ (c p) at i h≤ (h h∈ p)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`ν h) with nu h
    ... | h₁ , `lift h₂ = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂)))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at i h≤ h₁ , helper₃ Γᵃᵗ Γ x i h≤ h₂
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (h₁ , h₂) = helper₃ Γᵃᵗ Γ x i h≤ h₁ , helper₂ Γᵃᵗ Γ x at i h≤ h₂
    helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ (h₁ , h₂) = helper₂ Γᵃᵗ Γ x at₁ i h≤ h₁ , helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂
[at]|φ∧ψ|→[at]φ∧[at]ψ Γ x (+ˡ at) f'₁ f'₂ (h₁ , (h₂' , h₂'')) with [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at f'₁ f'₂ h₁
... | h₁' , h₁'' = (h₁' , h₂') , h₁'' , h₂''
[at]|φ∧ψ|→[at]φ∧[at]ψ Γ x (+ʳ at) f'₁ f'₂ ((h₁' , h₁'') , h₂) with [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at f'₁ f'₂ h₂
... | h₂' , h₂'' = (h₁' , h₂') , h₁'' , h₂''
[at]|φ∧ψ|→[at]φ∧[at]ψ Γ x (at₁ + at₂) f'₁ f'₂ (h₁ , h₂) with [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at₁ f'₁ f'₂ h₁ | [at]|φ∧ψ|→[at]φ∧[at]ψ Γ x at₂ f'₁ f'₂ h₂
... | h₁' , h₁'' | h₂' , h₂'' = (h₁' , h₂') , h₁'' , h₂''

[at]φ∧[at]ψ→[at]|φ∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (f'₁ f'₂ : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∀ at f'₁ ∧ at→af-∀ at f'₂ → Γ ⊢ x ⊨' at→af-∀ at (f'₁ ∧ f'₂)
[at]φ∧[at]ψ→[at]|φ∧ψ| _ _ ⦗ actF _ ⦘ _ _ (`[]-pure r h-eq₁ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | refl = `[]-pure r h-eq₁
[at]φ∧[at]ψ→[at]|φ∧ψ| _ _ ⦗ actF _ ⦘ _ _ (`[]-pure _ h-eq₁ , `[]-impure _ _ h-eq₂ _) with trans (sym h-eq₁) h-eq₂
... | ()
[at]φ∧[at]ψ→[at]|φ∧ψ| _ _ ⦗ actF _ ⦘ _ _ (`[]-impure _ _ h-eq₁ _ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | ()
[at]φ∧[at]ψ→[at]|φ∧ψ| Γ x ⦗ actF _ ⦘ f'₁ f'₂ (`[]-impure s c h-eq₁ h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
... | refl = `[]-impure s c h-eq₁ λ h∈ p → h₁ h∈ p , h₂ h∈ p
[at]φ∧[at]ψ→[at]|φ∧ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ f'₁ f'₂ (`ν h₁ , `ν h₂) = `ν (helper₁ Γ x h₁ h₂)
  where
  fp'₁' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁' = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift f'₁)

  fp'₁'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁'' = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift f'₂)

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift (f'₁ ∧ f'₂))

  helper₁ : (Γ  : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp'₁' [] → Nu Γ x fp'₁'' [] → Nu Γ x fp'₂ []
  nu (helper₁ Γ x h₁ h₂) = case nu h₁ of λ { (h₁' , `lift h₂') → case nu h₂ of λ { (h₁'' , `lift h₂'') → helper₂ [] Γ x at zero z≤n h₁' h₁'' , `lift (h₂' , h₂'') } }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h₁) (`ref h₂) = `ref (helper₁ Γ x h₁ h₂)
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h₁) (`ref h₂) with nu h₁ | nu h₂
    ... | h₁' , h₂' | h₁'' , h₂'' = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁' h₁'' , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₂' h₂''
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h₁) (`ref h₂) with nu h₁ | nu h₂
    ... | h₁' , (`lift h₂') | h₁'' , (`lift h₂'') = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁' h₁'' , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂' h₂'')
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-pure r h-eq₁) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-pure r h-eq₁
    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure _ h-eq₁) (`[]-impure _ _ h-eq₂ _) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-impure _ _ h-eq₁ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-impure s c h-eq₁ h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-impure s c h-eq₁ λ h∈ p → helper₃ Γᵃᵗ Γ (c p) i h≤ (h₁ h∈ p) (h₂ h∈ p)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`ν h₁) (`ν h₂) with nu h₁ | nu h₂
    ... | h₁' , (`lift h₂') | h₁'' , (`lift h₂'') = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁' h₁'' , `lift (helper₃ Γᵃᵗ Γ x i h≤ h₂' h₂'')))
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq₁) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-pure r h-eq₁
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure _ h-eq₁) (`[]-impure _ _ h-eq₂ _) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-impure _ _ h-eq₁ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`[]-impure s c h-eq₁ h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-impure s c h-eq₁ λ h∈ p → helper₂ Γᵃᵗ Γ (c p) at i h≤ (h₁ h∈ p) (h₂ h∈ p)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`ν h₁) (`ν h₂) with nu h₁ | nu h₂
    ... | h₁' , (`lift h₂') | h₁'' , (`lift h₂'') = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁' h₁'' , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂' h₂'')))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (h₁' , h₂') (h₁'' , h₂'') = helper₂ Γᵃᵗ Γ x at i h≤ h₁' h₁'' , helper₃ Γᵃᵗ Γ x i h≤ h₂' h₂''
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (h₁' , h₂') (h₁'' , h₂'') = helper₃ Γᵃᵗ Γ x i h≤ h₁' h₁'' , helper₂ Γᵃᵗ Γ x at i h≤ h₂' h₂''
    helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ (h₁' , h₂') (h₁'' , h₂'') = helper₂ Γᵃᵗ Γ x at₁ i h≤ h₁' h₁'' , helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂' h₂''
[at]φ∧[at]ψ→[at]|φ∧ψ| _ _ ((actF _) · _) _ _ (`[]-pure r h-eq₁ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | refl = `[]-pure r h-eq₁
[at]φ∧[at]ψ→[at]|φ∧ψ| _ _ ((actF _) · _) _ _ (`[]-pure _ h-eq₁ , `[]-impure _ _ h-eq₂ _) with trans (sym h-eq₁) h-eq₂
... | ()
[at]φ∧[at]ψ→[at]|φ∧ψ| _ _ ((actF _) · _) _ _ (`[]-impure _ _ h-eq₁ _ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | ()
[at]φ∧[at]ψ→[at]|φ∧ψ| Γ _ ((actF _) · at) f'₁ f'₂ (`[]-impure s c h-eq₁ h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
... | refl = `[]-impure s c h-eq₁ λ h∈ p → [at]φ∧[at]ψ→[at]|φ∧ψ| Γ (c p) at f'₁ f'₂ (h₁ h∈ p , h₂ h∈ p)
[at]φ∧[at]ψ→[at]|φ∧ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) f'₁ f'₂ (`ν h₁ , `ν h₂) = `ν (helper₁ Γ x h₁ h₂)
  where
  fp'₁' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁' = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ f'₁)

  fp'₁'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁'' = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ f'₂)

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (f'₁ ∧ f'₂))

  helper₁ : (Γ  : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp'₁' [] → Nu Γ x fp'₁'' [] → Nu Γ x fp'₂ []
  nu (helper₁ Γ x h₁ h₂) = case nu h₁ of λ { (h₁' , `lift h₂') → case nu h₂ of λ { (h₁'' , `lift h₂'') → helper₂ [] Γ x at₁ zero z≤n h₁' h₁'' , `lift ([at]φ∧[at]ψ→[at]|φ∧ψ| Γ x at₂ f'₁ f'₂ (h₂' , h₂'')) } }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp'₁') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h₁) (`ref h₂) = `ref (helper₁ Γ x h₁ h₂)
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h₁) (`ref h₂) with nu h₁ | nu h₂
    ... | h₁' , h₂' | h₁'' , h₂'' = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁' h₁'' , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₂' h₂''
    helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h₁) (`ref h₂) with nu h₁ | nu h₂
    ... | h₁' , (`lift h₂') | h₁'' , (`lift h₂'') = `ref helper
      where
      helper : Nu (Γᵃᵗ ++-∀ ((true , fp'₂) ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
      nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁' h₁'' , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂' h₂'')
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-pure r h-eq₁) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-pure r h-eq₁
    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-pure _ h-eq₁) (`[]-impure _ _ h-eq₂ _) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`[]-impure _ _ h-eq₁ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`[]-impure s c h-eq₁ h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-impure s c h-eq₁ λ h∈ p → helper₃ Γᵃᵗ Γ (c p) i h≤ (h₁ h∈ p) (h₂ h∈ p)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`ν h₁) (`ν h₂) with nu h₁ | nu h₂
    ... | h₁' , (`lift h₂') | h₁'' , (`lift h₂'') = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁' h₁'' , `lift (helper₃ Γᵃᵗ Γ x i h≤ h₂' h₂'')))
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq₁) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-pure r h-eq₁
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-pure _ h-eq₁) (`[]-impure _ _ h-eq₂ _) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ _ _ _ ((actF _) · _) _ _ (`[]-impure _ _ h-eq₁ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`[]-impure s c h-eq₁ h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `[]-impure s c h-eq₁ λ h∈ p → helper₂ Γᵃᵗ Γ (c p) at i h≤ (h₁ h∈ p) (h₂ h∈ p)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`ν h₁) (`ν h₂) with nu h₁ | nu h₂
    ... | h₁' , (`lift h₂') | h₁'' , (`lift h₂'') = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁' h₁'' , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂' h₂'')))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (h₁' , h₂') (h₁'' , h₂'') = helper₂ Γᵃᵗ Γ x at i h≤ h₁' h₁'' , helper₃ Γᵃᵗ Γ x i h≤ h₂' h₂''
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (h₁' , h₂') (h₁'' , h₂'') = helper₃ Γᵃᵗ Γ x i h≤ h₁' h₁'' , helper₂ Γᵃᵗ Γ x at i h≤ h₂' h₂''
    helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ (h₁' , h₂') (h₁'' , h₂'') = helper₂ Γᵃᵗ Γ x at₁ i h≤ h₁' h₁'' , helper₂ Γᵃᵗ Γ x at₂ i h≤ h₂' h₂''
[at]φ∧[at]ψ→[at]|φ∧ψ| Γ x (+ˡ at) f'₁ f'₂ ((h₁' , h₁'') , (h₂' , h₂'')) = [at]φ∧[at]ψ→[at]|φ∧ψ| Γ x at f'₁ f'₂ (h₁' , h₂') , h₁'' , h₂''
[at]φ∧[at]ψ→[at]|φ∧ψ| Γ x (+ʳ at) f'₁ f'₂ ((h₁' , h₁'') , (h₂' , h₂'')) = (h₁' , h₂') , [at]φ∧[at]ψ→[at]|φ∧ψ| Γ x at f'₁ f'₂ (h₁'' , h₂'')
[at]φ∧[at]ψ→[at]|φ∧ψ| Γ x (at₁ + at₂) f'₁ f'₂ ((h₁' , h₁'') , (h₂' , h₂'')) = [at]φ∧[at]ψ→[at]|φ∧ψ| Γ x at₁ f'₁ f'₂ (h₁' , h₂') , [at]φ∧[at]ψ→[at]|φ∧ψ| Γ x at₂ f'₁ f'₂ (h₁'' , h₂'')
