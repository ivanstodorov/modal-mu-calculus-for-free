{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Properties.Utils.RfConcatUtils where

open import Common.Biconditional using (_⇔_)
open import Common.Program using (Program)
open import Data.Container using (Container; Shape)
open import Data.Fin using (zero)
open import Data.List using (List; [])
open import Data.Product using (_,_)
open import Level using (Level)
open import ModalLogics.WithoutContainerizationNew.Base using (ActionNode; ActionTree; Arguments; Context; FixedPoint'; Formula'; Mu; Nu; _⊢_⊨'_; at→af-∀; at→af-∃; concatenate)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst; sym)

open ActionNode
open ActionTree
open Arguments
open FixedPoint'
open Formula'
open _⊢_⊨'_
open _≡_

private variable
  a s p r ℓ : Level
  α : Set a
  C : Container s p
  R : Set r
  prev : List (List (Set ℓ))

h-at→af-∃ : (at₁ at₂ : ActionTree α ℓ) → (f' : Formula' α ℓ prev) → at→af-∃ (concatenate at₁ at₂) f' ≡ at→af-∃ at₁ (at→af-∃ at₂ f')
h-at→af-∃ ⦗ actF _ ⦘ _ _ = refl
h-at→af-∃ ⦗ _ * ⦘ _ _ = refl
h-at→af-∃ ((actF af) · at₁) at₂ f' = cong (⟨_⟩_ af) (h-at→af-∃ at₁ at₂ f')
h-at→af-∃ ((at₁ *) · at₂) at₃ f' = cong₂ (λ fᵃᶠ₁ fᵃᶠ₂ → μ [] ． (formula (fᵃᶠ₁ ∨ lift fᵃᶠ₂))) refl (h-at→af-∃ at₂ at₃ f')
h-at→af-∃ (+ˡ at₁) at₂ f' = cong₂ _∨_ (h-at→af-∃ at₁ at₂ f') refl
h-at→af-∃ (+ʳ at₁) at₂ f' = cong₂ _∨_ refl (h-at→af-∃ at₁ at₂ f')
h-at→af-∃ (at₁ + at₂) at₃ f' = cong₂ _∨_ (h-at→af-∃ at₁ at₃ f') (h-at→af-∃ at₂ at₃ f')

⟨concatenate|at₁||at₂|⟩φ⇔⟨at₁⟩⟨at₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at₁ at₂ : ActionTree (Shape C) ℓ) → (f' : Formula' (Shape C) ℓ prev) → (Γ ⊢ x ⊨' at→af-∃ (concatenate at₁ at₂) f') ⇔ (Γ ⊢ x ⊨' at→af-∃ at₁ (at→af-∃ at₂ f'))
⟨concatenate|at₁||at₂|⟩φ⇔⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₂ f' = ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₂ f' , ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x at₁ at₂ f'
  where
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at₁ at₂ : ActionTree (Shape C) ℓ) → (f' : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∃ (concatenate at₁ at₂) f' → Γ ⊢ x ⊨' at→af-∃ at₁ (at→af-∃ at₂ f')
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ _ _ ⦗ actF _ ⦘ _ _ h = h
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ _ _ ⦗ _ * ⦘ _ _ h = h
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ _ ((actF _) · at₁) at₂ f' (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ (c p) at₁ at₂ f' h)
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x ((at₁ *) · at₂) at₃ f' (`μ h) = `μ (subst (λ fᵃᶠ → Mu Γ x (formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift fᵃᶠ)) []) (h-at→af-∃ at₂ at₃ f') h)
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x (+ˡ at₁) at₂ f' (inj₁ h) = inj₁ (⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₂ f' h)
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ _ _ (+ˡ _) _ _ (inj₂ h) = inj₂ h
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ _ _ (+ʳ _) _ _ (inj₁ h) = inj₁ h
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x (+ʳ at₁) at₂ f' (inj₂ h) = inj₂ (⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₂ f' h)
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x (at₁ + _) at₃ f' (inj₁ h) = inj₁ (⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x at₁ at₃ f' h)
  ⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x (_ + at₂) at₃ f' (inj₂ h) = inj₂ (⟨concatenate|at₁||at₂|⟩φ→⟨at₁⟩⟨at₂⟩φ Γ x at₂ at₃ f' h)

  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at₁ at₂ : ActionTree (Shape C) ℓ) → (f' : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∃ at₁ (at→af-∃ at₂ f') → Γ ⊢ x ⊨' at→af-∃ (concatenate at₁ at₂) f'
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ _ _ ⦗ actF _ ⦘ _ _ h = h
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ _ _ ⦗ _ * ⦘ _ _ h = h
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ _ ((actF _) · at₁) at₂ f' (`⟨⟩-impure s c h-eq h∈ p h) = `⟨⟩-impure s c h-eq h∈ p (⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ (c p) at₁ at₂ f' h)
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x ((at₁ *) · at₂) at₃ f' (`μ h) = `μ (subst (λ fᵃᶠ → Mu Γ x (formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift fᵃᶠ)) []) (sym (h-at→af-∃ at₂ at₃ f')) h)
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x (+ˡ at₁) at₂ f' (inj₁ h) = inj₁ (⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x at₁ at₂ f' h)
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ _ _ (+ˡ _) _ _ (inj₂ h) = inj₂ h
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ _ _ (+ʳ _) _ _ (inj₁ h) = inj₁ h
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x (+ʳ at₁) at₂ f' (inj₂ h) = inj₂ (⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x at₁ at₂ f' h)
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x (at₁ + _) at₃ f' (inj₁ h) = inj₁ (⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x at₁ at₃ f' h)
  ⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x (_ + at₂) at₃ f' (inj₂ h) = inj₂ (⟨at₁⟩⟨at₂⟩φ→⟨concatenate|at₁||at₂|⟩φ Γ x at₂ at₃ f' h)

h-at→af-∀ : (at₁ at₂ : ActionTree α ℓ) → (f' : Formula' α ℓ prev) → at→af-∀ (concatenate at₁ at₂) f' ≡ at→af-∀ at₁ (at→af-∀ at₂ f')
h-at→af-∀ ⦗ actF _ ⦘ _ _ = refl
h-at→af-∀ ⦗ _ * ⦘ _ _ = refl
h-at→af-∀ ((actF af) · at₁) at₂ fᵃᶠ = cong ([_]_ af) (h-at→af-∀ at₁ at₂ fᵃᶠ)
h-at→af-∀ ((at₁ *) · at₂) at₃ fᵃᶠ = cong₂ (λ fᵃᶠ₁ fᵃᶠ₂ → ν [] ． (formula (fᵃᶠ₁ ∧ lift fᵃᶠ₂))) refl (h-at→af-∀ at₂ at₃ fᵃᶠ)
h-at→af-∀ (+ˡ at₁) at₂ f' = cong₂ _∧_ (h-at→af-∀ at₁ at₂ f') refl
h-at→af-∀ (+ʳ at₁) at₂ f' = cong₂ _∧_ refl (h-at→af-∀ at₁ at₂ f')
h-at→af-∀ (at₁ + at₂) at₃ fᵃᶠ = cong₂ _∧_ (h-at→af-∀ at₁ at₃ fᵃᶠ) (h-at→af-∀ at₂ at₃ fᵃᶠ)

[concatenate|at₁||at₂|]φ⇔[at₁][at₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at₁ at₂ : ActionTree (Shape C) ℓ) → (f' : Formula' (Shape C) ℓ prev) → (Γ ⊢ x ⊨' at→af-∀ (concatenate at₁ at₂) f') ⇔ (Γ ⊢ x ⊨' at→af-∀ at₁ (at→af-∀ at₂ f'))
[concatenate|at₁||at₂|]φ⇔[at₁][at₂]φ Γ x at₁ at₂ f' = [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x at₁ at₂ f' , [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x at₁ at₂ f'
    where
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at₁ at₂ : ActionTree (Shape C) ℓ) → (f' : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∀ (concatenate at₁ at₂) f' → Γ ⊢ x ⊨' at→af-∀ at₁ (at→af-∀ at₂ f')
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ _ _ ⦗ actF _ ⦘ _ _ h = h
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ _ _ ⦗ _ * ⦘ _ _ h = h
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ _ ((actF _) · at₁) at₂ f' (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ (c p) at₁ at₂ f' (h h∈ p)
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x ((at₁ *) · at₂) at₃ f' (`ν h) = `ν (subst (λ fᵃᶠ → Nu Γ x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift fᵃᶠ)) []) (h-at→af-∀ at₂ at₃ f') h)
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x (+ˡ at₁) at₂ f' (h₁ , h₂) = [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x at₁ at₂ f' h₁ , h₂
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x (+ʳ at₁) at₂ f' (h₁ , h₂) = h₁ , [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x at₁ at₂ f' h₂
  [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x (at₁ + at₂) at₃ f' (h₁ , h₂) = [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x at₁ at₃ f' h₁ , [concatenate|at₁||at₂|]φ→[at₁][at₂]φ Γ x at₂ at₃ f' h₂

  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ : (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (at₁ at₂ : ActionTree (Shape C) ℓ) → (f' : Formula' (Shape C) ℓ prev) → Γ ⊢ x ⊨' at→af-∀ at₁ (at→af-∀ at₂ f') → Γ ⊢ x ⊨' at→af-∀ (concatenate at₁ at₂) f'
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ _ _ ⦗ actF _ ⦘ _ _ h = h
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ _ _ ⦗ _ * ⦘ _ _ h = h
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ _ _ ((actF _) · _) _ _ (`[]-pure r h-eq) = `[]-pure r h-eq
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ _ ((actF _) · at₂) at₃ f' (`[]-impure s c h-eq h) = `[]-impure s c h-eq λ h∈ p → [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ (c p) at₂ at₃ f' (h h∈ p)
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x ((at₁ *) · at₂) at₃ f' (`ν h) = `ν (subst (λ fᵃᶠ → Nu Γ x (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift fᵃᶠ)) []) (sym (h-at→af-∀ at₂ at₃ f')) h)
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x (+ˡ at₁) at₂ f' (h₁ , h₂) = [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x at₁ at₂ f' h₁ , h₂
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x (+ʳ at₁) at₂ f' (h₁ , h₂) = h₁ , [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x at₁ at₂ f' h₂
  [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x (at₁ + at₂) at₃ f' (h₁ , h₂) = [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x at₁ at₃ f' h₁ , [at₁][at₂]φ→[concatenate|at₁||at₂|]φ Γ x at₂ at₃ f' h₂
