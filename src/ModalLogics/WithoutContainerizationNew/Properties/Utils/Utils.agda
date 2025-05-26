{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.Utils.Utils where

open import Common.RegularFormulasWithData using (RegularFormula)
open import Data.Bool using (false; true)
open import Data.Fin using (zero)
open import Data.List using (List; replicate; _++_)
open import Data.Maybe using (nothing; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_,_)
open import Level using (Level; _⊔_) renaming (suc to sucˡ)
open import ModalLogics.WithoutContainerizationNew.Base using (ActionNode; ActionTree; Arguments; Context; FixedPoint'; Formula'; at→af-∀; at→af-∃; rf→at)
open import Relation.Binary.PropositionalEquality using (_≡_)

open RegularFormula
open List
open ℕ
open _≤_
open ActionNode
open ActionTree
open Arguments
open Context
open FixedPoint'
open Formula'
open _≡_

private variable
  a : Level

get-lift : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → (i j : ℕ) → i ≤ j → Formula' α ℓ (replicate j [] ++ ([] ∷ prev))
get-lift zero zero z≤n = ref zero ⦗ [] ⦘
get-lift zero (suc _) z≤n = ref zero ⦗ [] ⦘
get-lift (suc i) (suc j) (s≤s h) = lift get-lift i j h

data Contextᵃᵗ (α : Set a) (ℓ : Level) (prev : List (List (Set ℓ))) : ℕ → Set (a ⊔ sucˡ ℓ) where
  [] : Contextᵃᵗ α ℓ prev zero
  ⟮_,_⟯_∷_ : ∀ {j} → (i : ℕ) → i ≤ suc j → ActionTree α ℓ → Contextᵃᵗ α ℓ prev j → Contextᵃᵗ α ℓ prev (suc j)
  ⟮_,_⟯_＋_∷_ : ∀ {j} → (i : ℕ) → i ≤ j → ActionTree α ℓ → ActionTree α ℓ → Contextᵃᵗ α ℓ prev j → Contextᵃᵗ α ℓ prev (suc j)

_++-∃_ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {j : ℕ} → Contextᵃᵗ α ℓ prev j → Context α ℓ ([] ∷ prev) → Context α ℓ (replicate j [] ++ [] ∷ prev)
[] ++-∃ Γ = Γ
_++-∃_ {j = j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ = (false , formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ get-lift i j h≤)) ∷ (Γᵃᵗ ++-∃ Γ)
_++-∃_ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ = (false , formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift at→af-∃ at₂ (get-lift i j h≤))) ∷ (Γᵃᵗ ++-∃ Γ)

_++-∀_ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {j : ℕ} → Contextᵃᵗ α ℓ prev j → Context α ℓ ([] ∷ prev) → Context α ℓ (replicate j [] ++ [] ∷ prev)
[] ++-∀ Γ = Γ
_++-∀_ {j = j} (⟮ i , h≤ ⟯ at ∷ Γᵃᵗ) Γ = (true , formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ get-lift i j h≤)) ∷ (Γᵃᵗ ++-∀ Γ)
_++-∀_ {j = suc j} (⟮ i , h≤ ⟯ at₁ ＋ at₂ ∷ Γᵃᵗ) Γ = (true , formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ (get-lift i j h≤))) ∷ (Γᵃᵗ ++-∀ Γ)

h-rf→at-eq : {α : Set a} → {ℓ : Level} → (rf : RegularFormula α ℓ) → {at₁ at₂ : ActionTree α ℓ} → rf→at rf ≡ just at₁ → rf→at (rf *) ≡ just at₂ → ⦗ at₁ * ⦘ ≡ at₂
h-rf→at-eq rf h₁ h₂ with rf→at rf
h-rf→at-eq rf refl h₂ | just _ = just-injective h₂

h-rf→at-just : {α : Set a} → {ℓ : Level} → (rf : RegularFormula α ℓ) → {at : ActionTree α ℓ} → rf→at rf ≡ just at → rf→at (rf *) ≡ just ⦗ at * ⦘
h-rf→at-just rf h with rf→at rf
h-rf→at-just rf refl | just _ = refl

h-rf→at-nothing : {α : Set a} → {ℓ : Level} → (rf : RegularFormula α ℓ) → rf→at rf ≡ nothing → rf→at (rf *) ≡ nothing
h-rf→at-nothing rf h with rf→at rf
... | nothing = refl
