{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.Utils.RfDistribUtilsEx where

open import Common.Program using (Program)
open import Data.Bool using (false; true)
open import Data.Container using (Container; Shape)
open import Data.Fin using (zero)
open import Data.List using (List)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Function using (case_of_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (ActionNode; ActionTree; Arguments; Context; FixedPoint'; Formula'; Mu; Nu; _⊢_⊨'_; muᶜ; at→af-∀; at→af-∃)
open import ModalLogics.WithoutContainerizationNew.Properties.Utils.Utils using (Contextᵃᵗ; get-lift; _++-∀_; _++-∃_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans)

open List
open ℕ
open _≤_
open _⊎_
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

⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (f'₁ f'₂ : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∃ at (f'₁ ∨ f'₂) → Γ ⊢ x ⊨' at→af-∃ at f'₁ ∨ at→af-∃ at f'₂
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ _ _ ⦗ actF _ ⦘ _ _ (`⟨⟩-impure s c h-eq h∈ p (inj₁ h)) = inj₁ (`⟨⟩-impure s c h-eq h∈ p h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ _ _ ⦗ actF _ ⦘ _ _ (`⟨⟩-impure s c h-eq h∈ p (inj₂ h)) = inj₂ (`⟨⟩-impure s c h-eq h∈ p h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ f'₁ f'₂ (`μ h) = case helper₁ Γ x h of λ { (inj₁ h) → inj₁ (`μ h)
                                                                                                                  ; (inj₂ h) → inj₂ (`μ h) }
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift (f'₁ ∨ f'₂))

  fp'₂' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂' = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift f'₁)

  fp'₂'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂'' = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift f'₂)

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁ [] → Mu Γ x fp'₂' [] ⊎ Mu Γ x fp'₂'' []
  helper₁ Γ x h with mu h
  ... | inj₂ (`lift (inj₁ h)) = inj₁ (muᶜ (inj₂ (`lift h)))
  ... | inj₂ (`lift (inj₂ h)) = inj₂ (muᶜ (inj₂ (`lift h)))
  ... | inj₁ h = case helper₂ [] Γ x at zero z≤n h of λ { (inj₁ h) → inj₁ (muᶜ (inj₁ h))
                                                        ; (inj₂ h) → inj₂ (muᶜ (inj₁ h)) }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) ⊎ (Γᵃᵗ ++-∃ ((false , fp'₂'') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ ⊎ (Γᵃᵗ ++-∃ ((false , fp'₂'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) with helper₁ Γ x h
    ... | inj₁ h = inj₁ (`ref h)
    ... | inj₂ h = inj₂ (`ref h)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) with helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₁ h)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h))) with helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₂ h)))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₂ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) with helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₁ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h)))) with helper₂ Γᵃᵗ Γ x at₂ i h≤ h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₂ (`lift h))))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₂ (`lift h))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (`lift h)
    ... | inj₂ h = inj₂ (`lift h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (`lift h)
    ... | inj₂ h = inj₂ (`lift h)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq h∈ p h) with helper₃ Γᵃᵗ Γ (c p) i h≤ h
    ... | inj₁ h = inj₁ (`⟨⟩-impure s c h-eq h∈ p h)
    ... | inj₂ h = inj₂ (`⟨⟩-impure s c h-eq h∈ p h)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h))) with helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₁ h)))
    helper₂ Γᵃᵗ Γ x ⦗ _ * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h)))) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₂ (`lift h))))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₂ (`lift h))))
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq h∈ p h) with helper₂ Γᵃᵗ Γ (c p) at i h≤ h 
    ... | inj₁ h = inj₁ (`⟨⟩-impure s c h-eq h∈ p h)
    ... | inj₂ h = inj₂ (`⟨⟩-impure s c h-eq h∈ p h)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h))) with helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₁ h)))
    helper₂ Γᵃᵗ Γ x ((_ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h)))) with helper₂ Γᵃᵗ Γ x at₂ i h≤ h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₂ (`lift h))))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₂ (`lift h))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₁ h)
    ... | inj₂ h = inj₂ (inj₁ h)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (inj₂ h)
    ... | inj₂ h = inj₂ (inj₂ h)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (inj₁ h)
    ... | inj₂ h = inj₂ (inj₁ h)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₂ h)
    ... | inj₂ h = inj₂ (inj₂ h)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₁ h)
    ... | inj₂ h = inj₂ (inj₁ h)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₂ h)
    ... | inj₂ h = inj₂ (inj₂ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ _ ((actF _) · at) f'₁ f'₂ (`⟨⟩-impure s c h-eq h∈ p h) with ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ (c p) at f'₁ f'₂ h
... | inj₁ h = inj₁ (`⟨⟩-impure s c h-eq h∈ p h)
... | inj₂ h = inj₂ (`⟨⟩-impure s c h-eq h∈ p h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) f'₁ f'₂ (`μ h) = case helper₁ Γ x h of λ { (inj₁ h) → inj₁ (`μ h)
                                                                                                                         ; (inj₂ h) → inj₂ (`μ h) }
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift at→af-∃ at₂ (f'₁ ∨ f'₂))

  fp'₂' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂' = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift at→af-∃ at₂ f'₁)

  fp'₂'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂'' = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift at→af-∃ at₂ f'₂)

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁ [] → Mu Γ x fp'₂' [] ⊎ Mu Γ x fp'₂'' []
  helper₁ Γ x (muᶜ (inj₂ (`lift h))) with ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x at₂ f'₁ f'₂ h
  ... | inj₁ h = inj₁ (muᶜ (inj₂ (`lift h)))
  ... | inj₂ h = inj₂ (muᶜ (inj₂ (`lift h)))
  helper₁ Γ x (muᶜ (inj₁ h)) = case helper₂ [] Γ x at₁ zero z≤n h of λ { (inj₁ h) → inj₁ (muᶜ (inj₁ h))
                                                                       ; (inj₂ h) → inj₂ (muᶜ (inj₁ h)) }
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) ⊎ (Γᵃᵗ ++-∃ ((false , fp'₂'') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ ⊎ (Γᵃᵗ ++-∃ ((false , fp'₂'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) with helper₁ Γ x h
    ... | inj₁ h = inj₁ (`ref h)
    ... | inj₂ h = inj₂ (`ref h)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) with helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₁ h)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h))) with helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₂ h)))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₂ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) with helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₁ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h)))) with helper₂ Γᵃᵗ Γ x at₂ i h≤ h
    ... | inj₁ h = inj₁ (`ref (muᶜ (inj₂ (`lift h))))
    ... | inj₂ h = inj₂ (`ref (muᶜ (inj₂ (`lift h))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (`lift h)
    ... | inj₂ h = inj₂ (`lift h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (`lift h)
    ... | inj₂ h = inj₂ (`lift h)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq h∈ p h) with helper₃ Γᵃᵗ Γ (c p) i h≤ h
    ... | inj₁ h = inj₁ (`⟨⟩-impure s c h-eq h∈ p h)
    ... | inj₂ h = inj₂ (`⟨⟩-impure s c h-eq h∈ p h)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h))) with helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₁ h)))
    helper₂ Γᵃᵗ Γ x ⦗ _ * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h)))) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₂ (`lift h))))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₂ (`lift h))))
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq h∈ p h) with helper₂ Γᵃᵗ Γ (c p) at i h≤ h 
    ... | inj₁ h = inj₁ (`⟨⟩-impure s c h-eq h∈ p h)
    ... | inj₂ h = inj₂ (`⟨⟩-impure s c h-eq h∈ p h)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h))) with helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₁ h)))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₁ h)))
    helper₂ Γᵃᵗ Γ x ((_ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h)))) with helper₂ Γᵃᵗ Γ x at₂ i h≤ h
    ... | inj₁ h = inj₁ (`μ (muᶜ (inj₂ (`lift h))))
    ... | inj₂ h = inj₂ (`μ (muᶜ (inj₂ (`lift h))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₁ h)
    ... | inj₂ h = inj₂ (inj₁ h)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (inj₂ h)
    ... | inj₂ h = inj₂ (inj₂ h)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) with helper₃ Γᵃᵗ Γ x i h≤ h
    ... | inj₁ h = inj₁ (inj₁ h)
    ... | inj₂ h = inj₂ (inj₁ h)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₂ h)
    ... | inj₂ h = inj₂ (inj₂ h)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₁ h)
    ... | inj₂ h = inj₂ (inj₁ h)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) with helper₂ Γᵃᵗ Γ x at i h≤ h
    ... | inj₁ h = inj₁ (inj₂ h)
    ... | inj₂ h = inj₂ (inj₂ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (+ˡ at) f'₁ f'₂ (inj₁ h) with ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x at f'₁ f'₂ h
... | inj₁ h = inj₁ (inj₁ h)
... | inj₂ h = inj₂ (inj₁ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (+ˡ at) f'₁ f'₂ (inj₂ (inj₁ h)) = inj₁ (inj₂ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (+ˡ at) f'₁ f'₂ (inj₂ (inj₂ h)) = inj₂ (inj₂ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (+ʳ at) f'₁ f'₂ (inj₁ (inj₁ h)) = inj₁ (inj₁ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (+ʳ at) f'₁ f'₂ (inj₁ (inj₂ h)) = inj₂ (inj₁ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (+ʳ at) f'₁ f'₂ (inj₂ h) with ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x at f'₁ f'₂ h
... | inj₁ h = inj₁ (inj₂ h)
... | inj₂ h = inj₂ (inj₂ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (at + _) f'₁ f'₂ (inj₁ h) with ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x at f'₁ f'₂ h
... | inj₁ h = inj₁ (inj₁ h)
... | inj₂ h = inj₂ (inj₁ h)
⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x (_ + at) f'₁ f'₂ (inj₂ h) with ⟨at⟩|φ∨ψ|→⟨at⟩φ∨⟨at⟩ψ Γ x at f'₁ f'₂ h
... | inj₁ h = inj₁ (inj₂ h)
... | inj₂ h = inj₂ (inj₂ h)

⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (f'₁ f'₂ : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∃ at f'₁ ∨ at→af-∃ at f'₂ → Γ ⊢ x ⊨' at→af-∃ at (f'₁ ∨ f'₂)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| _ _ ⦗ actF _ ⦘ _ _ (inj₁ (`⟨⟩-impure s c h-eq h∈ p h)) = `⟨⟩-impure s c h-eq h∈ p (inj₁ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| _ _ ⦗ actF _ ⦘ _ _ (inj₂ (`⟨⟩-impure s c h-eq h∈ p h)) = `⟨⟩-impure s c h-eq h∈ p (inj₂ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ f'₁ f'₂ (inj₁ (`μ h)) = `μ (helper₁ Γ x h)
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift f'₁)

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift (f'₁ ∨ f'₂))

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁ [] → Mu Γ x fp'₂ []
  helper₁ Γ x (muᶜ (inj₂ (`lift h))) = muᶜ (inj₂ (`lift (inj₁ h)))
  helper₁ Γ x (muᶜ (inj₁ h)) = muᶜ (inj₁ (helper₂ [] Γ x at zero z≤n h))
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁ Γ x h)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h))) = `ref (muᶜ (inj₂ (helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h)))) = `ref (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₃ Γᵃᵗ Γ (c p) i h≤ h)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ⦗ _ * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₃ Γᵃᵗ Γ x i h≤ h))))
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₂ Γᵃᵗ Γ (c p) at i h≤ h)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) = inj₂ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) = inj₁ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ f'₁ f'₂ (inj₂ (`μ h)) = `μ (helper₁ Γ x h)
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift f'₂)

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift (f'₁ ∨ f'₂))

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁ [] → Mu Γ x fp'₂ []
  helper₁ Γ x (muᶜ (inj₂ (`lift h))) = muᶜ (inj₂ (`lift (inj₂ h)))
  helper₁ Γ x (muᶜ (inj₁ h)) = muᶜ (inj₁ (helper₂ [] Γ x at zero z≤n h))
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁ Γ x h)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h))) = `ref (muᶜ (inj₂ (helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h)))) = `ref (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₃ Γᵃᵗ Γ (c p) i h≤ h)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ⦗ _ * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₃ Γᵃᵗ Γ x i h≤ h))))
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₂ Γᵃᵗ Γ (c p) at i h≤ h)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) = inj₂ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) = inj₁ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x ((actF _) · at) f'₁ f'₂ (inj₁ (`⟨⟩-impure s c h-eq h∈ p h)) = `⟨⟩-impure s c h-eq h∈ p (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ (c p) at f'₁ f'₂ (inj₁ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x ((actF _) · at) f'₁ f'₂ (inj₂ (`⟨⟩-impure s c h-eq h∈ p h)) = `⟨⟩-impure s c h-eq h∈ p (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ (c p) at f'₁ f'₂ (inj₂ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) f'₁ f'₂ (inj₁ (`μ h)) = `μ (helper₁ Γ x h)
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift (at→af-∃ at₂ f'₁))

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift (at→af-∃ at₂ (f'₁ ∨ f'₂)))

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁ [] → Mu Γ x fp'₂ []
  helper₁ Γ x (muᶜ (inj₂ (`lift h))) = muᶜ (inj₂ (`lift (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at₂ f'₁ f'₂ (inj₁ h))))
  helper₁ Γ x (muᶜ (inj₁ h)) = muᶜ (inj₁ (helper₂ [] Γ x at₁ zero z≤n h))
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁ Γ x h)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h))) = `ref (muᶜ (inj₂ (helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h)))) = `ref (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₃ Γᵃᵗ Γ (c p) i h≤ h)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ⦗ _ * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₃ Γᵃᵗ Γ x i h≤ h))))
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₂ Γᵃᵗ Γ (c p) at i h≤ h)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) = inj₂ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) = inj₁ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) f'₁ f'₂ (inj₂ (`μ h)) = `μ (helper₁ Γ x h)
  where
  fp'₁ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁ = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift (at→af-∃ at₂ f'₂))

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift (at→af-∃ at₂ (f'₁ ∨ f'₂)))

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁ [] → Mu Γ x fp'₂ []
  helper₁ Γ x (muᶜ (inj₂ (`lift h))) = muᶜ (inj₂ (`lift (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at₂ f'₁ f'₂ (inj₂ h))))
  helper₁ Γ x (muᶜ (inj₁ h)) = muᶜ (inj₁ (helper₂ [] Γ x at₁ zero z≤n h))
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h) = `ref (helper₁ Γ x h)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h))) = `ref (muᶜ (inj₂ (helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h))) = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h)))) = `ref (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h)

    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₃ Γᵃᵗ Γ (c p) i h≤ h)
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ⦗ _ * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₃ Γᵃᵗ Γ x i h≤ h))))
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (helper₂ Γᵃᵗ Γ (c p) at i h≤ h)
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h))) = `μ (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h)))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h)))) = `μ (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h) = inj₂ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h) = inj₁ (helper₃ Γᵃᵗ Γ x i h≤ h)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ˡ at) f'₁ f'₂ (inj₁ (inj₁ h)) = inj₁ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₁ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ˡ at) f'₁ f'₂ (inj₁ (inj₂ h)) = inj₂ (inj₁ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ˡ at) f'₁ f'₂ (inj₂ (inj₁ h)) = inj₁ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₂ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ˡ at) f'₁ f'₂ (inj₂ (inj₂ h)) = inj₂ (inj₂ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ʳ at) f'₁ f'₂ (inj₁ (inj₁ h)) = inj₁ (inj₁ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ʳ at) f'₁ f'₂ (inj₁ (inj₂ h)) = inj₂ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₁ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ʳ at) f'₁ f'₂ (inj₂ (inj₁ h)) = inj₁ (inj₂ h)
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (+ʳ at) f'₁ f'₂ (inj₂ (inj₂ h)) = inj₂ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₂ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (at + _) f'₁ f'₂ (inj₁ (inj₁ h)) = inj₁ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₁ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (_ + at) f'₁ f'₂ (inj₁ (inj₂ h)) = inj₂ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₁ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (at + _) f'₁ f'₂ (inj₂ (inj₁ h)) = inj₁ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₂ h))
⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x (_ + at) f'₁ f'₂ (inj₂ (inj₂ h)) = inj₂ (⟨at⟩φ∨⟨at⟩ψ→⟨at⟩|φ∨ψ| Γ x at f'₁ f'₂ (inj₂ h))

⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (f'₁ f'₂ : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∃ at f'₁ ∧ at→af-∀ at f'₂ → Γ ⊢ x ⊨' at→af-∃ at (f'₁ ∧ f'₂)
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| _ _ ⦗ actF _ ⦘ _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | ()
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| _ _ ⦗ actF _ ⦘ _ _ (`⟨⟩-impure s c h-eq₁ h∈ p h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (h₁ , h₂ h∈ p)
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ⦗ at * ⦘ f'₁ f'₂ (`μ h₁ , `ν h₂) = `μ (helper₁ Γ x h₁ h₂)
  where
  fp'₁' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁' = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift f'₁)

  fp'₁'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁'' = formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift f'₂)

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift (f'₁ ∧ f'₂))

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁' [] → Nu Γ x fp'₁'' [] → Mu Γ x fp'₂ []
  helper₁ Γ x (muᶜ (inj₂ (`lift h₁))) h₂ with nu h₂
  ... | _ , `lift h₂ = muᶜ (inj₂ (`lift (h₁ , h₂)))
  helper₁ Γ x (muᶜ (inj₁ h₁-∃)) h₂ with nu h₂
  ... | h₂-∀ , _ = muᶜ (inj₁ (helper₂ [] Γ x at zero z≤n h₁-∃ h₂-∀))
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h₁) (`ref h₂) = `ref (helper₁ Γ x h₁ h₂)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h₁))) (`ref h₂) with nu h₂
    ... | h₂ , _ = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ h₂)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h₁))) (`ref h₂) with nu h₂
    ... | _ , h₂ = `ref (muᶜ (inj₂ (helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₁ h₂)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h₁))) (`ref h₂) with nu h₂
    ... | h₂ , _ = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ h₂)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h₁)))) (`ref h₂) with nu h₂
    ... | _ , `lift h₂ = `ref (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₁ h₂))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)

    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq₁ h∈ p h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (helper₃ Γᵃᵗ Γ (c p) i h≤ h₁ (h₂ h∈ p))
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h₁))) (`ν h₂) with nu h₂
    ... | h₂ , _ = `μ (muᶜ (inj₁ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ h₂)))
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h₁)))) (`ν h₂) with nu h₂
    ... | _ , `lift h₂ = `μ (muᶜ (inj₂ (`lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂))))
    helper₂ _ _ _ ((actF _) · _) _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq₁ h∈ p h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (helper₂ Γᵃᵗ Γ (c p) at i h≤ h₁ (h₂ h∈ p))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h₁))) (`ν h₂) with nu h₂
    ... | h₂ , _ = `μ (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ h₂)))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h₁)))) (`ν h₂) with nu h₂
    ... | _ , `lift h₂ = `μ (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₁ h₂))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h₁) (h₂ , _) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h₁) (_ , h₂) = inj₂ (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h₁) (h₂ , _) = inj₁ (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h₁) (_ , h₂) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h₁) (h₂ , _) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h₁) (_ , h₂) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| _ _ ((actF _) · _) _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _ , `[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
... | ()
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ _ ((actF _) · at) f'₁ f'₂ (`⟨⟩-impure s c h-eq₁ h∈ p h₁ , `[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ (c p) at f'₁ f'₂ (h₁ , h₂ h∈ p))
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| {C = C} {ℓ = ℓ} {prev = prev} {R = R} Γ x ((at₁ *) · at₂) f'₁ f'₂ (`μ h₁ , `ν h₂) = `μ (helper₁ Γ x h₁ h₂)
  where
  fp'₁' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁' = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift (at→af-∃ at₂ f'₁))

  fp'₁'' : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₁'' = formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift (at→af-∀ at₂ f'₂))

  fp'₂ : FixedPoint' (Shape C) ℓ ([] ∷ prev) []
  fp'₂ = formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift (at→af-∃ at₂ (f'₁ ∧ f'₂)))

  helper₁ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → Mu Γ x fp'₁' [] → Nu Γ x fp'₁'' [] → Mu Γ x fp'₂ []
  helper₁ Γ x (muᶜ (inj₂ (`lift h₁))) h₂ with nu h₂
  ... | _ , `lift h₂ = muᶜ (inj₂ (`lift (⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x at₂ f'₁ f'₂ (h₁ , h₂))))
  helper₁ Γ x (muᶜ (inj₁ h₁-∃)) h₂ with nu h₂
  ... | h₂-∀ , _ = muᶜ (inj₁ (helper₂ [] Γ x at₁ zero z≤n h₁-∃ h₂-∀))
    where
    helper₂ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at : ActionTree (Shape C) ℓ) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁') ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤) → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' at→af-∀ at (get-lift i j h≤) → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' at→af-∃ at (get-lift i j h≤)

    helper₃ : {j : ℕ} → (Γᵃᵗ : Contextᵃᵗ (Shape C) ℓ prev j) → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : ℕ) → (h≤ : i ≤ j) → (Γᵃᵗ ++-∃ ((false , fp'₁') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∀ ((true , fp'₁'') ∷ Γ)) ⊢ x ⊨' get-lift i j h≤ → (Γᵃᵗ ++-∃ ((false , fp'₂) ∷ Γ)) ⊢ x ⊨' get-lift i j h≤
    helper₃ [] Γ x zero z≤n (`ref h₁) (`ref h₂) = `ref (helper₁ Γ x h₁ h₂)
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h₁))) (`ref h₂) with nu h₂
    ... | h₂ , _ = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ h₂)))
    helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ h₁))) (`ref h₂) with nu h₂
    ... | _ , h₂ = `ref (muᶜ (inj₂ (helper₃ (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ x i h≤ h₁ h₂)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₁ h₁))) (`ref h₂) with nu h₂
    ... | h₂ , _ = `ref (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ h₂)))
    helper₃ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x zero z≤n (`ref (muᶜ (inj₂ (`lift h₁)))) (`ref h₂) with nu h₂
    ... | _ , `lift h₂ = `ref (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₁ h₂))))
    helper₃ (⟮ _ , _ ⟯ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₃ (⟮ _ , _ ⟯ _ ＋ _ ∷ Γᵃᵗ) Γ x (suc i) (s≤s h≤) (`lift h₁) (`lift h₂) = `lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)

    helper₂ _ _ _ ⦗ actF _ ⦘ _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ⦗ actF _ ⦘ i h≤ (`⟨⟩-impure s c h-eq₁ h∈ p h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (helper₃ Γᵃᵗ Γ (c p) i h≤ h₁ (h₂ h∈ p))
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₁ h₁))) (`ν h₂) with nu h₂
    ... | h₂ , _ = `μ (muᶜ (inj₁ (helper₂ (⟮ suc i , s≤s h≤ ⟯ at ∷ Γᵃᵗ) Γ x at zero z≤n h₁ h₂)))
    helper₂ Γᵃᵗ Γ x ⦗ at * ⦘ i h≤ (`μ (muᶜ (inj₂ (`lift h₁)))) (`ν h₂) with nu h₂
    ... | _ , `lift h₂ = `μ (muᶜ (inj₂ (`lift (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂))))
    helper₂ _ _ _ ((actF _) · _) _ _ (`⟨⟩-impure _ _ h-eq₁ _ _ _) (`[]-pure _ h-eq₂) with trans (sym h-eq₁) h-eq₂
    ... | ()
    helper₂ Γᵃᵗ Γ _ ((actF _) · at) i h≤ (`⟨⟩-impure s c h-eq₁ h∈ p h₁) (`[]-impure _ _ h-eq₂ h₂) with trans (sym h-eq₁) h-eq₂
    ... | refl = `⟨⟩-impure s c h-eq₁ h∈ p (helper₂ Γᵃᵗ Γ (c p) at i h≤ h₁ (h₂ h∈ p))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₁ h₁))) (`ν h₂) with nu h₂
    ... | h₂ , _ = `μ (muᶜ (inj₁ (helper₂ (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ x at₁ zero z≤n h₁ h₂)))
    helper₂ Γᵃᵗ Γ x ((at₁ *) · at₂) i h≤ (`μ (muᶜ (inj₂ (`lift h₁)))) (`ν h₂) with nu h₂
    ... | _ , `lift h₂ = `μ (muᶜ (inj₂ (`lift (helper₂ Γᵃᵗ Γ x at₂ i h≤ h₁ h₂))))
    helper₂ Γᵃᵗ Γ x (+ˡ at) i h≤ (inj₁ h₁) (h₂ , _) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (+ˡ _) i h≤ (inj₂ h₁) (_ , h₂) = inj₂ (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (+ʳ _) i h≤ (inj₁ h₁) (h₂ , _) = inj₁ (helper₃ Γᵃᵗ Γ x i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (+ʳ at) i h≤ (inj₂ h₁) (_ , h₂) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (at + _) i h≤ (inj₁ h₁) (h₂ , _) = inj₁ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
    helper₂ Γᵃᵗ Γ x (_ + at) i h≤ (inj₂ h₁) (_ , h₂) = inj₂ (helper₂ Γᵃᵗ Γ x at i h≤ h₁ h₂)
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x (+ˡ at) f'₁ f'₂ (inj₁ h₁-∃ , (h₂-∀ , _)) = inj₁ (⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x at f'₁ f'₂ (h₁-∃ , h₂-∀))
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| _ _ (+ˡ _) _ _ (inj₂ h₁ , (_ , h₂)) = inj₂ (h₁ , h₂)
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| _ _ (+ʳ _) _ _ (inj₁ h₁ , (h₂ , _)) = inj₁ (h₁ , h₂)
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x (+ʳ at) f'₁ f'₂ (inj₂ h₁-∃ , (_ , h₂-∀)) = inj₂ (⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x at f'₁ f'₂ (h₁-∃ , h₂-∀))
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x (at₁ + at₂) f'₁ f'₂ (inj₁ h₁-∃ , (h₂-∀ , _)) = inj₁ (⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x at₁ f'₁ f'₂ (h₁-∃ , h₂-∀))
⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x (at₁ + at₂) f'₁ f'₂ (inj₂ h₁-∃ , (_ , h₂-∀)) = inj₂ (⟨at⟩φ∧[at]ψ→⟨at⟩|φ∧ψ| Γ x at₂ f'₁ f'₂ (h₁-∃ , h₂-∀))
