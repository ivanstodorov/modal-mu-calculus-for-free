{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerization.BaseList where

open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula; _∈_)
open import Data.Bool using (Bool; not; T)
open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; toℕ; cast; inject₁)
open import Data.Fin.Properties using (cast-is-id)
open import Data.List using (List; length; map) renaming (_++_ to _++ˡ_)
open import Data.List.NonEmpty using (List⁺; head; tail; toList) renaming (_∷_ to _∷⁺_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-map; length-++)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _<ᵇ_; _≥_; _<_; _<?_; suc; s≤s)
open import Data.Nat.Properties using (+-suc; ≮⇒≥; <⇒<ᵇ; <ᵇ⇒<; m≤n⇒m<n∨m≡n)
open import Data.Product using (_×_; _,_; map₁; map₂; proj₂; ∃-syntax)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (⊤)
open import Function using (case_of_; _∘_; id)
open import Level using (Lift; Level; _⊔_) renaming (suc to sucˡ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (subst; sym; _≡_; inspect; cong; trans) renaming ([_] to [_]⁼)
open import Relation.Nullary using (no; yes; ¬_)

open RegularFormula
open Bool
open Fin
open List
open Maybe
open _≡_

private variable
  a s p r : Level

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {T params} → T → Arguments ℓ params → Arguments ℓ (T ∷ params)

dropˡ : {α : Set a} → (xs : List α) → (i : Fin (length xs)) → List⁺ α
dropˡ (x ∷ xs) zero = x ∷⁺ xs
dropˡ (_ ∷ xs) (suc i) = dropˡ xs i

infix 60 val_
infix 60 ref_⦗_⦘
-- infix 55 ~_
infix 50 ⟨_⟩_
infix 50 [_]_
infixr 45 _∧_
infixr 40 _∨_
-- infixr 35 _⇒_
infix 30 ∀⦗_⦘_
infix 30 ∃⦗_⦘_
-- infix 30 μ_．_
-- infix 30 ν_．_

data Formulaᵃᶠ (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → Set (a ⊔ sucˡ ℓ)

data Parameterizedᵃᶠ (α : Set a) (ℓ : Level) (prev : List (List (Set ℓ))) : List (Set ℓ) → Set (a ⊔ sucˡ ℓ) where
  formula_ : Formulaᵃᶠ α ℓ prev → Parameterizedᵃᶠ α ℓ prev []
  _＝_↦_ : ∀ {params} → (T : Set ℓ) → T → (T → Parameterizedᵃᶠ α ℓ prev params) → Parameterizedᵃᶠ α ℓ prev (T ∷ params)

data Formulaᵃᶠ α ℓ where
  true false : ∀ {prev} → Formulaᵃᶠ α ℓ prev
  val_ : ∀ {prev} → Set ℓ → Formulaᵃᶠ α ℓ prev
  _∧_ _∨_ : ∀ {prev} → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {prev} → (T : Set ℓ) → (T → Formulaᵃᶠ α ℓ prev) → Formulaᵃᶠ α ℓ prev
  ⟨_⟩_ [_]_ : ∀ {prev} → ActionFormula α ℓ → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev
  μ_ ν_ : ∀ {prev params} → Parameterizedᵃᶠ α ℓ (params ∷ prev) params → Formulaᵃᶠ α ℓ prev
  ref_⦗_⦘ : ∀ {prev} → (i : Fin (length prev)) → Arguments ℓ (head (dropˡ prev i)) → Formulaᵃᶠ α ℓ prev

applyᵃᶠ-d : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Formulaᵃᶠ α ℓ prev
applyᵃᶠ-d (formula fᵃᶠ) = fᵃᶠ
applyᵃᶠ-d (_ ＝ t ↦ pᵃᶠ) = applyᵃᶠ-d (pᵃᶠ t)

applyᵃᶠ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Arguments ℓ params → Formulaᵃᶠ α ℓ prev
applyᵃᶠ (formula fᵃᶠ) _ = fᵃᶠ
applyᵃᶠ (_ ＝ _ ↦ pᵃᶠ) (t ∷ args) = applyᵃᶠ (pᵃᶠ t) args

data History (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → List (List (Set ℓ)) → Set (a ⊔ sucˡ ℓ) where
  [] : ∀ {prev : List (List (Set ℓ))} → History α ℓ [] prev
  _∷_ : ∀ {prev₁ prev₂ : List (List (Set ℓ))} {params : List (Set ℓ)} → Bool × Parameterizedᵃᶠ α ℓ ((params ∷ prev₁) ++ˡ prev₂) params → History α ℓ prev₁ prev₂ → History α ℓ (params ∷ prev₁) prev₂

drop : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → History α ℓ prev₁ prev₂ → (i : Fin (length prev₁)) → History α ℓ (toList (dropˡ prev₁ i)) prev₂
drop hist@(_ ∷ _) zero = hist
drop (_ ∷ hist) (suc i) = drop hist i

_++'_ : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → History α ℓ prev₁ prev₂ → History α ℓ prev₂ [] → History α ℓ (prev₁ ++ˡ prev₂) []
[] ++' hist₂ = hist₂
_++'_ {α = α} {ℓ = ℓ} {prev₁ = params ∷ prev₁} {prev₂ = prev₂} ((flag , pᵃᶠ) ∷ hist₁) hist₂ = (flag , subst (λ xs → Parameterizedᵃᶠ α ℓ (params ∷ xs) params) (sym (++-identityʳ (prev₁ ++ˡ prev₂))) pᵃᶠ) ∷ (hist₁ ++' hist₂)

infix 25 _⊨ᵃᶠ_｛_｝

_⊨ᵃᶠ_｛_｝ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev : List (List (Set ℓ))} → Program C R → Formulaᵃᶠ (Shape C) ℓ prev → History (Shape C) ℓ prev [] → Set (s ⊔ p ⊔ ℓ)

record Mu {C : Container s p} {R : Set r} {ℓ : Level} {prev : List (List (Set ℓ))} (x : Program C R) (f : Formulaᵃᶠ (Shape C) ℓ prev) (hist : History (Shape C) ℓ prev []) : Set (s ⊔ p ⊔ ℓ) where
  inductive
  constructor muᶜ
  field
    mu : x ⊨ᵃᶠ f ｛ hist ｝

record Nu {C : Container s p} {R : Set r} {ℓ : Level} {prev : List (List (Set ℓ))} (x : Program C R) (f : Formulaᵃᶠ (Shape C) ℓ prev) (hist : History (Shape C) ℓ prev []) : Set (s ⊔ p ⊔ ℓ) where
  coinductive
  constructor nuᶜ
  field
    nu : x ⊨ᵃᶠ f ｛ hist ｝

_ ⊨ᵃᶠ true ｛ _ ｝ = ⊤
_ ⊨ᵃᶠ false ｛ _ ｝ = ⊥
_⊨ᵃᶠ_｛_｝ {s = s} {p = p} {ℓ = ℓ} _ (val x) _ = Lift (s ⊔ p ⊔ ℓ) x
x ⊨ᵃᶠ fᵃᶠ₁ ∧ fᵃᶠ₂ ｛ hist ｝ = x ⊨ᵃᶠ fᵃᶠ₁ ｛ hist ｝ × x ⊨ᵃᶠ fᵃᶠ₂ ｛ hist ｝
x ⊨ᵃᶠ fᵃᶠ₁ ∨ fᵃᶠ₂ ｛ hist ｝ = x ⊨ᵃᶠ fᵃᶠ₁ ｛ hist ｝ ⊎ x ⊨ᵃᶠ fᵃᶠ₂ ｛ hist ｝
x ⊨ᵃᶠ ∀⦗ _ ⦘ fᵃᶠ ｛ hist ｝ = ∀ t → x ⊨ᵃᶠ fᵃᶠ t ｛ hist ｝
x ⊨ᵃᶠ ∃⦗ _ ⦘ fᵃᶠ ｛ hist ｝ = ∃[ t ] x ⊨ᵃᶠ fᵃᶠ t ｛ hist ｝
x ⊨ᵃᶠ ⟨ af ⟩ fᵃᶠ ｛ hist ｝ with free x
... | pure _ = ⊥
... | impure (s , c) = s ∈ af × ∃[ p ] c p ⊨ᵃᶠ fᵃᶠ ｛ hist ｝
x ⊨ᵃᶠ [ af ] fᵃᶠ ｛ hist ｝ with free x
... | pure _ = ⊤
... | impure (s , c) = s ∈ af → ∀ p → c p ⊨ᵃᶠ fᵃᶠ ｛ hist ｝
_⊨ᵃᶠ_｛_｝ {C = C} {ℓ = ℓ} {prev = prev} x (μ_ {params = params} pᵃᶠ) hist = Mu x (applyᵃᶠ-d pᵃᶠ) ((false , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (params ∷ xs) params) (sym (++-identityʳ prev)) pᵃᶠ) ∷ hist)
_⊨ᵃᶠ_｛_｝ {C = C} {ℓ = ℓ} {prev = prev} x (ν_ {params = params} pᵃᶠ) hist = Nu x (applyᵃᶠ-d pᵃᶠ) ((true , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (params ∷ xs) params) (sym (++-identityʳ prev)) pᵃᶠ) ∷ hist)
_⊨ᵃᶠ_｛_｝ {C = C} {ℓ = ℓ} {prev = prev} x ref i ⦗ args ⦘ hist with drop hist i
... | hist@(_∷_ {params = params} (false , pᵃᶠ) _) = Mu x (applyᵃᶠ (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (params ∷ xs) params) (++-identityʳ (tail (dropˡ prev i))) pᵃᶠ) args) hist
... | hist@(_∷_ {params = params} (true , pᵃᶠ) _) = Nu x (applyᵃᶠ (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (params ∷ xs) params) (++-identityʳ (tail (dropˡ prev i))) pᵃᶠ) args) hist



open import Data.Empty using (⊥-elim)
open import Data.Nat using (z<s; s<s; _>_) renaming (_≟_ to _≟ⁿ_)
open import Data.Nat.Properties using (suc-injective)
open import Relation.Binary.PropositionalEquality using (_≢_)

open ℕ
open Mu
open Nu
open _⊎_

test' : {ℓ : Level} → {α : Set ℓ} → (xs₁ xs₂ : List α) → (x : α) → (i : Fin (length (xs₁ ++ˡ x ∷ xs₂))) → (h : toℕ i ≡ length xs₁) → x ∷⁺ xs₂ ≡ dropˡ (xs₁ ++ˡ x ∷ xs₂) i
test' [] _ _ zero _ = refl
test' (_ ∷ xs₁) xs₂ x (suc i) h = test' xs₁ xs₂ x i (suc-injective h)

h-drop-≡ : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params : List (Set ℓ)} → (i : Fin (length (prev₁ ++ˡ params ∷ prev₂))) → (hist₁ : History α ℓ prev₁ (params ∷ prev₂)) → (hist₂ : History α ℓ prev₂ []) → (flag : Bool) → (pᵃᶠ : Parameterizedᵃᶠ α ℓ (params ∷ prev₂ ++ˡ []) params) → (h : toℕ i ≡ length prev₁) → drop (hist₁ ++' ((flag , pᵃᶠ) ∷ hist₂)) i ≡ (flag , subst (λ xs → Parameterizedᵃᶠ α ℓ (head xs ∷ tail xs ++ˡ []) (head xs)) (test' prev₁ prev₂ params i h) pᵃᶠ) ∷ subst (λ xs → History α ℓ (tail xs) []) (test' prev₁ prev₂ params i h) hist₂
h-drop-≡ zero [] _ _ _ _ = refl
h-drop-≡ (suc i) (_ ∷ hist₁) hist₂ flag pᵃᶠ h = h-drop-≡ i hist₁ hist₂ flag pᵃᶠ (suc-injective h)

h-drop-< : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params : List (Set ℓ)} → (i : Fin (length (prev₁ ++ˡ params ∷ prev₂))) → (hist₁ : History α ℓ prev₁ (params ∷ prev₂)) → (hist₂ : History α ℓ prev₂ []) → (flag₁ flag₂ : Bool) → (pᵃᶠ₁ pᵃᶠ₂ : Parameterizedᵃᶠ α ℓ (params ∷ prev₂ ++ˡ []) params) → (h : toℕ i > length prev₁) → drop (hist₁ ++' ((flag₁ , pᵃᶠ₁) ∷ hist₂)) i ≡ drop (hist₁ ++' ((flag₂ , pᵃᶠ₂) ∷ hist₂)) i
h-drop-< (suc _) [] _ _ _ _ _ _ = refl
h-drop-< (suc i) (_ ∷ hist₁) hist₂ flag₁ flag₂ pᵃᶠ₁ pᵃᶠ₂ (s≤s h) = h-drop-< i hist₁ hist₂ flag₁ flag₂ pᵃᶠ₁ pᵃᶠ₂ h

subst-prev : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → (x : Program C R) → (fᵃᶠ : Formulaᵃᶠ (Shape C) ℓ (prev₁ ++ˡ [] ∷ prev₂)) → (flag : Bool) → (fᵃᶠ₁ fᵃᶠ₂ : Formulaᵃᶠ (Shape C) ℓ ([] ∷ prev₂)) → (hist₁ : History (Shape C) ℓ prev₁ ([] ∷ prev₂)) → (hist₂ : History (Shape C) ℓ prev₂ []) → let h = sym (++-identityʳ prev₂) in ((x' : Program C R) → x' ⊨ᵃᶠ fᵃᶠ₁ ｛ (flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) ∷ hist₂ ｝ → x' ⊨ᵃᶠ fᵃᶠ₂ ｛ (flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) ∷ hist₂ ｝) → x ⊨ᵃᶠ fᵃᶠ ｛ hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) ∷ hist₂) ｝ → x ⊨ᵃᶠ fᵃᶠ ｛ hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂)) ∷ hist₂) ｝

subst-prev-pᵈ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params : List (Set ℓ)} → (x : Program C R) → (pᵃᶠ : Parameterizedᵃᶠ (Shape C) ℓ (prev₁ ++ˡ [] ∷ prev₂) params) → (flag : Bool) → (fᵃᶠ₁ fᵃᶠ₂ : Formulaᵃᶠ (Shape C) ℓ ([] ∷ prev₂)) → (hist₁ : History (Shape C) ℓ prev₁ ([] ∷ prev₂)) → (hist₂ : History (Shape C) ℓ prev₂ []) → let h = sym (++-identityʳ prev₂) in ((x' : Program C R) → x' ⊨ᵃᶠ fᵃᶠ₁ ｛ (flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₁)) ∷ hist₂ ｝ → x' ⊨ᵃᶠ fᵃᶠ₂ ｛ (flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₁)) ∷ hist₂ ｝) → x ⊨ᵃᶠ applyᵃᶠ-d pᵃᶠ ｛ hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₁)) ∷ hist₂) ｝ → x ⊨ᵃᶠ applyᵃᶠ-d pᵃᶠ ｛ hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₂)) ∷ hist₂) ｝
subst-prev-pᵈ x (formula fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h = subst-prev x fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h
subst-prev-pᵈ x (_ ＝ t ↦ pᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h = subst-prev-pᵈ x (pᵃᶠ t) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h

subst-prev-p : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params : List (Set ℓ)} → (x : Program C R) → (pᵃᶠ : Parameterizedᵃᶠ (Shape C) ℓ (prev₁ ++ˡ [] ∷ prev₂) params) → (args : Arguments ℓ params) → (flag : Bool) → (fᵃᶠ₁ fᵃᶠ₂ : Formulaᵃᶠ (Shape C) ℓ ([] ∷ prev₂)) → (hist₁ : History (Shape C) ℓ prev₁ ([] ∷ prev₂)) → (hist₂ : History (Shape C) ℓ prev₂ []) → let h = sym (++-identityʳ prev₂) in ((x' : Program C R) → x' ⊨ᵃᶠ fᵃᶠ₁ ｛ (flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₁)) ∷ hist₂ ｝ → x' ⊨ᵃᶠ fᵃᶠ₂ ｛ (flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₁)) ∷ hist₂ ｝) → x ⊨ᵃᶠ applyᵃᶠ pᵃᶠ args ｛ hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₁)) ∷ hist₂) ｝ → x ⊨ᵃᶠ applyᵃᶠ pᵃᶠ args ｛ hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) h (formula fᵃᶠ₂)) ∷ hist₂) ｝
subst-prev-p x (formula fᵃᶠ) [] flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h = subst-prev x fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h
subst-prev-p x (_ ＝ _ ↦ pᵃᶠ) (t ∷ args) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h = subst-prev-p x (pᵃᶠ t) args flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h

subst-prev _ true _ _ _ _ _ _ h = h
subst-prev _ (val _) _ _ _ _ _ _ h = h
subst-prev x (fᵃᶠ' ∧ fᵃᶠ'') flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (h₁ , h₂) = subst-prev x fᵃᶠ' flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h₁ , subst-prev x fᵃᶠ'' flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h₂
subst-prev x (fᵃᶠ ∨ _) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (inj₁ h) = inj₁ (subst-prev x fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h)
subst-prev x (_ ∨ fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (inj₂ h) = inj₂ (subst-prev x fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h)
subst-prev x (∀⦗ T ⦘ fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h t = subst-prev x (fᵃᶠ t) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (h t)
subst-prev x (∃⦗ T ⦘ fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (t , h) = t , subst-prev x (fᵃᶠ t) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h
subst-prev x (⟨ af ⟩ fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h with free x
subst-prev x (⟨ af ⟩ fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (h∈ , p , h) | impure (_ , c) = h∈ , p , subst-prev (c p) fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h
subst-prev x ([ af ] fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h with free x
... | pure _ = h
... | impure (_ , c) = λ h∈ p → subst-prev (c p) fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ (h h∈ p)
mu (subst-prev x (μ pᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h) = subst-prev-pᵈ x pᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ ((false , pᵃᶠ) ∷ hist₁) hist₂ h→ (mu h)
nu (subst-prev x (ν pᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h) = subst-prev-pᵈ x pᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ ((true , pᵃᶠ) ∷ hist₁) hist₂ h→ (nu h)
subst-prev {C = C} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h with drop (hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) ∷ hist₂)) i | inspect (drop (hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) ∷ hist₂))) i | drop (hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂)) ∷ hist₂)) i | inspect (drop (hist₁ ++' ((flag , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂)) ∷ hist₂))) i
... | drop₁ | [ eq₁ ]⁼ | drop₂ | [ eq₂ ]⁼ with length prev₁ <? (toℕ i)
...   | yes h< with trans (sym eq₁) (trans (h-drop-< i hist₁ hist₂ flag flag (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂)) h<) eq₂)
...     | refl = h
subst-prev {C = C} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | drop₁ | [ eq₁ ]⁼ | drop₂ | [ eq₂ ]⁼ | no h≮ with m≤n⇒m<n∨m≡n (≮⇒≥ h≮)
subst-prev {C = C} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | x₁ ∷ drop₁ | [ eq₁ ]⁼ | x₂ ∷ drop₂ | [ eq₂ ]⁼ | no h≮ | inj₂ h≡ with trans (sym eq₁) ((h-drop-≡ i hist₁ hist₂ flag (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁)) h≡)) | trans (sym eq₂) ((h-drop-≡ i hist₁ hist₂ flag (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂)) h≡))
subst-prev {C = C} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} x ref i ⦗ args ⦘ false fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | .(false , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (head xs ∷ tail xs ++ˡ []) (head xs)) (test' prev₁ prev₂ [] i h≡) (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁))) ∷ .(subst (λ xs → History (Shape C) ℓ (tail xs) []) (test' prev₁ prev₂ [] i h≡) hist₂) | [ eq₁ ]⁼ | .(false , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (head xs ∷ tail xs ++ˡ []) (head xs)) (test' prev₁ prev₂ [] i h≡) (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂))) ∷ .(subst (λ xs → History (Shape C) ℓ (tail xs) []) (test' prev₁ prev₂ [] i h≡) hist₂) | [ eq₂ ]⁼ | no h≮ | inj₂ h≡ | refl | refl = {!   !}
subst-prev {C = C} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} x ref i ⦗ args ⦘ true fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | .(true , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (head xs ∷ tail xs ++ˡ []) (head xs)) (test' prev₁ prev₂ [] i h≡) (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₁))) ∷ .(subst (λ xs → History (Shape C) ℓ (tail xs) []) (test' prev₁ prev₂ [] i h≡) hist₂) | [ eq₁ ]⁼ | .(true , subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ (head xs ∷ tail xs ++ˡ []) (head xs)) (test' prev₁ prev₂ [] i h≡) (subst (λ xs → Parameterizedᵃᶠ (Shape C) ℓ ([] ∷ xs) []) (sym (++-identityʳ prev₂)) (formula fᵃᶠ₂))) ∷ .(subst (λ xs → History (Shape C) ℓ (tail xs) []) (test' prev₁ prev₂ [] i h≡) hist₂) | [ eq₂ ]⁼ | no h≮ | inj₂ h≡ | refl | refl = {!   !}
subst-prev {C = C} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | drop₁ | [ eq₁ ]⁼ | drop₂ | [ eq₂ ]⁼ | no h≮ | inj₁ h> = {!   !}
