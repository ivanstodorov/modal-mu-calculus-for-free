{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.Utils.RfConstUtils where

open import Common.Program using (impure; pure; free; Program)
open import Data.Bool using (false; true)
open import Data.Container using (Container; Shape)
open import Data.Fin using (zero)
open import Data.List using (List)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (ActionNode; ActionTree; Arguments; Context; FixedPoint'; Formula'; Mu; Nu; _⊢_⊨'_; nuᶜ; at→af-∀; at→af-∃)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.Utils using (Contextᵃᵗ; get-lift; _++-∀_; _++-∃_)
open import Relation.Binary.PropositionalEquality using (inspect) renaming ([_] to [_]⁼)

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
open Mu
open Nu
open _⊢_⊨'_

private variable
  s p r ℓ : Level
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))

⟨at⟩false→false : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → Γ ⊢ x ⊨' at→af-∃ at false → Γ ⊢ x ⊨' false
⟨at⟩false→false _ _ ⦗ actF _ ⦘ (`⟨⟩-impure _ _ _ _ _ ())
⟨at⟩false→false {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ (`μ h) = helper₁ Γ x h
  where
  fp' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp' = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift false)

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp' [] → Γ ⊢ x ⊨' false
  helper₁ Γ x h with mu h
  ... | inj₂ (`lift ())
  ... | inj₁ h = case helper₂ [] Γ x at zero z≤n h of λ ()
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' false

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' false
    helper₃ [] Γ x zero z≤n (`ref h) = case helper₁ Γ x h of λ ()
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with mu h
    ... | inj₁ h = case helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h of λ ()
    ... | inj₂ h = case helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h of λ ()
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with mu h
    ... | inj₁ h = case helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h of λ ()
    ... | inj₂ (`lift h) = case helper₂ Γᵃᵗ Γ x at₂ i h≤ h of λ ()
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure _ c _ _ p h) = case helper₃ Γᵃᵗ Γ (c p) i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ h) with mu h
    ... | inj₁ h = case helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h of λ ()
    ... | inj₂ (`lift h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure _ c _ _ p h) = case helper₂ Γᵃᵗ Γ (c p) at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ h) with mu h
    ... | inj₁ h = case helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h of λ ()
    ... | inj₂ (`lift h) = case helper₂ Γᵃᵗ Γ x at₂ i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
⟨at⟩false→false Γ _ ((actF _) · at) (`⟨⟩-impure _ c _ _ p h) = case ⟨at⟩false→false Γ (c p) at h of λ ()
⟨at⟩false→false {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) (`μ h) = helper₁ Γ x h
  where
  fp' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp' = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift at→af-∃ at₂ false)

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp' [] → Γ ⊢ x ⊨' false
  helper₁ Γ x h with mu h
  ... | inj₂ (`lift h) = case ⟨at⟩false→false Γ x at₂ h of λ ()
  ... | inj₁ h = case helper₂ [] Γ x at₁ zero z≤n h of λ ()
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' false

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp') ∷ Γ)) ⊢ x ⊨' false
    helper₃ [] Γ x zero z≤n (`ref h) = case helper₁ Γ x h of λ ()
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with mu h
    ... | inj₁ h = case helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h of λ ()
    ... | inj₂ h = case helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h of λ ()
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref h) with mu h
    ... | inj₁ h = case helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h of λ ()
    ... | inj₂ (`lift h) = case helper₂ Γᵃᵗ Γ x at₂ i h≤ h of λ ()
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure _ c _ _ p h) = case helper₃ Γᵃᵗ Γ (c p) i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ h) with mu h
    ... | inj₁ h = case helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h of λ ()
    ... | inj₂ (`lift h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure _ c _ _ p h) = case helper₂ Γᵃᵗ Γ (c p) at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ h) with mu h
    ... | inj₁ h = case helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h of λ ()
    ... | inj₂ (`lift h) = case helper₂ Γᵃᵗ Γ x at₂ i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) = case helper₃ Γᵃᵗ Γ x i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) = case helper₂ Γᵃᵗ Γ x at i h≤ h of λ ()
⟨at⟩false→false Γ x (+ˡ at) (inj₁ h) = ⟨at⟩false→false Γ x at h
⟨at⟩false→false Γ x (+ʳ at) (inj₂ h) = ⟨at⟩false→false Γ x at h
⟨at⟩false→false Γ x (at + _) (inj₁ h) = ⟨at⟩false→false Γ x at h
⟨at⟩false→false Γ x (_ + at) (inj₂ h) = ⟨at⟩false→false Γ x at h

[at]true : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → Γ ⊢ x ⊨' at→af-∀ at true
[at]true _ x ⦗ actF _ ⦘ with free x | inspect free x
... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ _ → `true
[at]true {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ = `ν (helper₁ Γ x)
  where
  fp' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp' = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift true)

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp' []
  nu (helper₁ Γ x) = helper₂ [] Γ x at zero z≤n , `lift `true
    where
      helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

      helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
      helper₃ [] Γ x zero z≤n = `ref (helper₁ Γ x)
      helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n = `ref helper
        where
        helper : Nu (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
        nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤
      helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n = `ref helper
        where
        helper : Nu (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
        nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤)
      helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) = `lift (helper₃ Γᵃᵗ Γ x i h≤)
      helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) = `lift (helper₃ Γᵃᵗ Γ x i h≤)

      helper₂ Γᵃᵗ Γ x ⦗ actF _ ⦘ i h≤ with free x | inspect free x
      ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
      ... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ p → helper₃ Γᵃᵗ Γ (c p) i h≤
      helper₂ {j = j} Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n , `lift (helper₃ Γᵃᵗ Γ x i h≤)))
      helper₂ Γᵃᵗ Γ x ((actF _) · at) i h≤ with free x | inspect free x
      ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
      ... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ p → helper₂ Γᵃᵗ Γ (c p) at i h≤
      helper₂ {j = j} Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤)))
      helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ = helper₂ Γᵃᵗ Γ x at i h≤ , helper₃ Γᵃᵗ Γ x i h≤
      helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ = helper₃ Γᵃᵗ Γ x i h≤ , helper₂ Γᵃᵗ Γ x at i h≤
      helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ = helper₂ Γᵃᵗ Γ x at₁ i h≤ , helper₂ Γᵃᵗ Γ x at₂ i h≤
[at]true Γ x ((actF _) · at) with free x | inspect free x
... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ p → [at]true Γ (c p) at
[at]true {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) = `ν (helper₁ Γ x)
  where
  fp' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp' = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ true)

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Nu Γ x fp' []
  nu (helper₁ Γ x) = helper₂ [] Γ x at₁ zero z≤n , `lift ([at]true Γ x at₂)
    where
      helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤)

      helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
      helper₃ [] Γ x zero z≤n = `ref (helper₁ Γ x)
      helper₃ {j = suc j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n = `ref helper
        where
        helper : Nu (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) x (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i (suc j) h≤)) []
        nu helper = helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n , helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤
      helper₃ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n = `ref helper
        where
        helper : Nu (Γᵃᵗ ++-∀ ((true , fp') ∷ Γ)) x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) []
        nu helper = helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤)
      helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) = `lift (helper₃ Γᵃᵗ Γ x i h≤)
      helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) = `lift (helper₃ Γᵃᵗ Γ x i h≤)

      helper₂ Γᵃᵗ Γ x ⦗ actF _ ⦘ i h≤ with free x | inspect free x
      ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
      ... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ p → helper₃ Γᵃᵗ Γ (c p) i h≤
      helper₂ {j = j} Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ = `ν (nuᶜ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n , `lift (helper₃ Γᵃᵗ Γ x i h≤)))
      helper₂ Γᵃᵗ Γ x ((actF _) · at) i h≤ with free x | inspect free x
      ... | pure r | [ h-eq ]⁼ = `[]-pure r h-eq
      ... | impure (s , c) | [ h-eq ]⁼ = `[]-impure s c h-eq λ _ p → helper₂ Γᵃᵗ Γ (c p) at i h≤
      helper₂ {j = j} Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ = `ν (nuᶜ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n , `lift (helper₂ Γᵃᵗ Γ x at₂ i h≤)))
      helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ = helper₂ Γᵃᵗ Γ x at i h≤ , helper₃ Γᵃᵗ Γ x i h≤
      helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ = helper₃ Γᵃᵗ Γ x i h≤ , helper₂ Γᵃᵗ Γ x at i h≤
      helper₂ Γᵃᵗ Γ x (at₁ + at₂) i h≤ = helper₂ Γᵃᵗ Γ x at₁ i h≤ , helper₂ Γᵃᵗ Γ x at₂ i h≤
[at]true Γ x (+ˡ at) = [at]true Γ x at , `true
[at]true Γ x (+ʳ at) = `true , [at]true Γ x at
[at]true Γ x (at₁ + at₂) = [at]true Γ x at₁ , [at]true Γ x at₂
