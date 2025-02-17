{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerization.Base where

open import Common.Program using (pure; impure; Program; free)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula; _∈_)
open import Data.Bool using (Bool; not; T)
open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; cast; inject₁; toℕ)
open import Data.Fin.Properties using (cast-is-id)
open import Data.List using (List; length; map) renaming (_++_ to _++ˡ_)
open import Data.List.Properties using (length-map; length-++; ++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe)
open import Data.Nat using (suc; s≤s; _≥_; _<_; _<ᵇ_)
open import Data.Nat.Properties using (+-suc; ≮⇒≥; <⇒<ᵇ; <ᵇ⇒<)
open import Data.Product using (_,_; _×_; map₁; map₂; proj₂; ∃-syntax; Σ-syntax)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (fromList) renaming (lookup to lookupᵛ)
open import Function using (case_of_; _∘_)
open import Level using (Lift; Level; _⊔_) renaming (suc to sucˡ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; inspect; trans; cong) renaming ([_] to [_]⁼)
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

find : {ℓ₁ ℓ₂ : Level} → {α : Set ℓ₁} → {β : Set ℓ₂} → (xs : List (α × β)) → α → DecidableEquality α → Maybe (Fin (length xs) × β)
find [] _ _ = nothing
find ((a₁ , b) ∷ xs) a₂ _≟_ with a₁ ≟ a₂
... | yes _ = just (zero , b)
... | no _ with find xs a₂ _≟_
...   | just (i , b) = just (suc i , b)
...   | nothing = nothing

infix 60 val_
infix 60 ref_⦗_⦘
infix 55 ~_
infix 50 ⟨_⟩_
infix 50 [_]_
infixr 45 _∧_
infixr 40 _∨_
infixr 35 _⇒_
infix 30 ∀⦗_⦘_
infix 30 ∃⦗_⦘_
infix 30 μ_．_
infix 30 ν_．_

data Formulaʳᶠ (α : Set a) (ℓ : Level) : List (String × Bool × List (Set ℓ)) → Set (a ⊔ sucˡ ℓ)

infix 70 formula_
infix 65 _＝_↦_

data Parameterizedʳᶠ (α : Set a) (ℓ : Level) (prev : List (String × Bool × List (Set ℓ))) : List (Set ℓ) → Set (a ⊔ sucˡ ℓ) where
  formula_ : Formulaʳᶠ α ℓ prev → Parameterizedʳᶠ α ℓ prev []
  _＝_↦_ : ∀ {params} → (T : Set ℓ) → T → (T → Parameterizedʳᶠ α ℓ prev params) → Parameterizedʳᶠ α ℓ prev (T ∷ params)

data Formulaʳᶠ α ℓ where
  true false : ∀ {prev} → Formulaʳᶠ α ℓ prev
  val_ : ∀ {prev} → Set ℓ → Formulaʳᶠ α ℓ prev
  ~_ : ∀ {prev} → Formulaʳᶠ α ℓ (map (map₂ (map₁ not)) prev) → Formulaʳᶠ α ℓ prev
  _∧_ _∨_ : ∀ {prev} → Formulaʳᶠ α ℓ prev → Formulaʳᶠ α ℓ prev → Formulaʳᶠ α ℓ prev
  _⇒_ : ∀ {prev} → Formulaʳᶠ α ℓ (map (map₂ (map₁ not)) prev) → Formulaʳᶠ α ℓ prev → Formulaʳᶠ α ℓ prev
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {prev} → (T : Set ℓ) → (T → Formulaʳᶠ α ℓ prev) → Formulaʳᶠ α ℓ prev
  ⟨_⟩_ [_]_ : ∀ {prev} → RegularFormula α ℓ → Formulaʳᶠ α ℓ prev → Formulaʳᶠ α ℓ prev
  μ_．_ ν_．_ : ∀ {prev params} → (name : String) → Parameterizedʳᶠ α ℓ ((name , true , params) ∷ prev) params → Formulaʳᶠ α ℓ prev
  ref_⦗_⦘ : ∀ {prev} → (name : String) → case find prev name _≟_ of (λ { (just (_ , true , αs)) → Arguments ℓ αs
                                                                       ; _ → ⊥ }) → Formulaʳᶠ α ℓ prev

applyʳᶠ-d : {α : Set a} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedʳᶠ α ℓ prev params → Formulaʳᶠ α ℓ prev
applyʳᶠ-d (formula fʳᶠ) = fʳᶠ
applyʳᶠ-d (_ ＝ t ↦ pʳᶠ) = applyʳᶠ-d (pʳᶠ t)

applyʳᶠ : {α : Set a} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedʳᶠ α ℓ prev params → Arguments ℓ params → Formulaʳᶠ α ℓ prev
applyʳᶠ (formula fʳᶠ) _ = fʳᶠ
applyʳᶠ (_ ＝ _ ↦ pʳᶠ) (t ∷ args) = applyʳᶠ (pʳᶠ t) args

data ActionTree (α : Set a) (ℓ : Level) : Set (a ⊔ sucˡ ℓ)

data ActionNode (α : Set a) (ℓ : Level) : Set (a ⊔ sucˡ ℓ) where
  ε : ActionNode α ℓ
  actF_ : ActionFormula α ℓ → ActionNode α ℓ
  _* : ActionTree α ℓ → ActionNode α ℓ

data ActionTree α ℓ where
  ⦗_⦘ : ActionNode α ℓ → ActionTree α ℓ
  _·_ : ActionNode α ℓ → ActionTree α ℓ → ActionTree α ℓ
  _+_ : ActionTree α ℓ → ActionTree α ℓ → ActionTree α ℓ

concatenate : {α : Set a} → {ℓ : Level} → ActionTree α ℓ → ActionTree α ℓ → ActionTree α ℓ
concatenate ⦗ x ⦘ at₂ = x · at₂
concatenate (x · at₁) at₂ = x · concatenate at₁ at₂
concatenate (at₁ + at₂) at₃ = concatenate at₁ at₃ + concatenate at₂ at₃

rf→at : {α : Set a} → {ℓ : Level} → RegularFormula α ℓ → ActionTree α ℓ
rf→at ε = ⦗ ε ⦘
rf→at (actF af) = ⦗ actF af ⦘
rf→at (rf₁ · rf₂) = concatenate (rf→at rf₁) (rf→at rf₂)
rf→at (rf₁ + rf₂) = rf→at rf₁ + rf→at rf₂
rf→at (rf *) = ⦗ rf→at rf * ⦘
rf→at (rf ⁺) = let at = rf→at rf in concatenate at ⦗ at * ⦘

data Formulaᵃᵗ (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → Set (a ⊔ sucˡ ℓ)

data Parameterizedᵃᵗ (α : Set a) (ℓ : Level) (prev : List (List (Set ℓ))) : List (Set ℓ) → Set (a ⊔ sucˡ ℓ) where
  formula_ : Formulaᵃᵗ α ℓ prev → Parameterizedᵃᵗ α ℓ prev []
  _＝_↦_ : ∀ {params} → (T : Set ℓ) → T → (T → Parameterizedᵃᵗ α ℓ prev params) → Parameterizedᵃᵗ α ℓ prev (T ∷ params)

data Formulaᵃᵗ α ℓ where
  true false : ∀ {prev} → Formulaᵃᵗ α ℓ prev
  val_ : ∀ {prev} → Set ℓ → Formulaᵃᵗ α ℓ prev
  _∧_ _∨_ : ∀ {prev} → Formulaᵃᵗ α ℓ prev → Formulaᵃᵗ α ℓ prev → Formulaᵃᵗ α ℓ prev
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {prev} → (T : Set ℓ) → (T → Formulaᵃᵗ α ℓ prev) → Formulaᵃᵗ α ℓ prev
  ⟨_⟩_ [_]_ : ∀ {prev} → ActionTree α ℓ → Formulaᵃᵗ α ℓ prev → Formulaᵃᵗ α ℓ prev
  μ_ ν_ : ∀ {prev params} → Parameterizedᵃᵗ α ℓ (params ∷ prev) params → Formulaᵃᵗ α ℓ prev
  ref_⦗_⦘ : ∀ {prev} → (i : Fin (length prev)) → Arguments ℓ (lookupᵛ (fromList prev) i) → Formulaᵃᵗ α ℓ prev

applyᵃᵗ-d : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᵗ α ℓ prev params → Formulaᵃᵗ α ℓ prev
applyᵃᵗ-d (formula fᵃᵗ) = fᵃᵗ
applyᵃᵗ-d (_ ＝ t ↦ pᵃᵗ) = applyᵃᵗ-d (pᵃᵗ t)

applyᵃᵗ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᵗ α ℓ prev params → Arguments ℓ params → Formulaᵃᵗ α ℓ prev
applyᵃᵗ (formula fᵃᵗ) _ = fᵃᵗ
applyᵃᵗ (_ ＝ _ ↦ pᵃᵗ) (t ∷ args) = applyᵃᵗ (pᵃᵗ t) args

h-map : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} → {α : Set ℓ₁} → {β : Set ℓ₂} → {γ : Set ℓ₃} → {δ : Set ℓ₄} → (xs : List (α × β × γ)) → (f : β → δ) → map (proj₂ ∘ proj₂) (map (map₂ (map₁ f)) xs) ≡ map (proj₂ ∘ proj₂) xs
h-map [] _ = refl
h-map ((a , b , c) ∷ xs) f = helper refl (h-map xs f)
  where
  helper : {ℓ : Level} → {α : Set ℓ} → {x y : α} → {xs ys : List α} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
  helper {x = x} {y = y} {xs = xs} {ys = ys} fst snd = subst (λ a → x ∷ xs ≡ a ∷ ys) fst (subst (λ as → x ∷ xs ≡ x ∷ as) snd refl)

h-lookup : {ℓ : Level} → (prev : List (String × Bool × List (Set ℓ))) → {x : String} → {i : Fin (length prev)} → {flag : Bool} → {params : List (Set ℓ)} → find prev x _≟_ ≡ just (i , flag , params) → params ≡ lookupᵛ (fromList (map (proj₂ ∘ proj₂) prev)) (cast (sym (length-map (proj₂ ∘ proj₂) prev)) i)
h-lookup ((name , _ , _) ∷ prev) {x = x} h with name ≟ x
h-lookup ((name , _ , _) ∷ prev) {x = .name} refl | yes refl = refl
... | no _ with find prev x _≟_ | inspect (find prev x) _≟_
... | just _ | [ eq ]⁼ with h-lookup prev eq
h-lookup ((name , _ , _) ∷ prev) {x = x} refl | no _ | just _ | [ eq ]⁼ | refl = refl

fʳᶠ→fᵃᵗ : {α : Set a} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → Formulaʳᶠ α ℓ prev → Formulaᵃᵗ α ℓ (map (proj₂ ∘ proj₂) prev)

pʳᶠ→pᵃᵗ : {α : Set a} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedʳᶠ α ℓ prev params → Parameterizedᵃᵗ α ℓ (map (proj₂ ∘ proj₂) prev) params
pʳᶠ→pᵃᵗ (formula fʳᶠ) = formula fʳᶠ→fᵃᵗ fʳᶠ
pʳᶠ→pᵃᵗ (T ＝ t ↦ pʳᶠ) = T ＝ t ↦ (pʳᶠ→pᵃᵗ ∘ pʳᶠ)

negate : {α : Set a} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → Formulaʳᶠ α ℓ prev → Formulaᵃᵗ α ℓ (map (proj₂ ∘ proj₂) prev)

negate-p : {α : Set a} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedʳᶠ α ℓ prev params → Parameterizedᵃᵗ α ℓ (map (proj₂ ∘ proj₂) prev) params
negate-p (formula fʳᶠ) = formula negate fʳᶠ
negate-p (T ＝ t ↦ pʳᶠ) = T ＝ t ↦ (negate-p ∘ pʳᶠ)

negate true = false
negate false = true
negate (val x) = val (¬ x)
negate {α = α} {ℓ = ℓ} {prev = prev} (~ fʳᶠ) = subst (Formulaᵃᵗ α ℓ) (h-map prev not) (fʳᶠ→fᵃᵗ fʳᶠ)
negate (fʳᶠ₁ ∧ fʳᶠ₂) = negate fʳᶠ₁ ∨ negate fʳᶠ₂
negate (fʳᶠ₁ ∨ fʳᶠ₂) = negate fʳᶠ₁ ∧ negate fʳᶠ₂
negate {α = α} {ℓ = ℓ} {prev = prev} (fʳᶠ₁ ⇒ fʳᶠ₂) = subst (Formulaᵃᵗ α ℓ) (h-map prev not) (fʳᶠ→fᵃᵗ fʳᶠ₁) ∧ negate fʳᶠ₂
negate (∀⦗ T ⦘ fʳᶠ) = ∃⦗ T ⦘ (negate ∘ fʳᶠ)
negate (∃⦗ T ⦘ fʳᶠ) = ∀⦗ T ⦘ (negate ∘ fʳᶠ)
negate (⟨ rf ⟩ fʳᶠ) = [ rf→at rf ] negate fʳᶠ
negate ([ rf ] fʳᶠ) = ⟨ rf→at rf ⟩ negate fʳᶠ
negate (μ name ． pʳᶠ) = ν negate-p pʳᶠ
negate (ν name ． pʳᶠ) = μ negate-p pʳᶠ
negate {ℓ = ℓ} {prev = prev} ref name ⦗ args ⦘ with find prev name _≟_ | inspect (find prev name) _≟_
... | just (i , true , αs) | [ eq ]⁼ = ref cast (sym (length-map (proj₂ ∘ proj₂) prev)) i ⦗ subst (Arguments ℓ) (h-lookup prev eq) args ⦘

fʳᶠ→fᵃᵗ true = true
fʳᶠ→fᵃᵗ false = false
fʳᶠ→fᵃᵗ (val x) = val x
fʳᶠ→fᵃᵗ {α = α} {ℓ = ℓ} {prev = prev} (~ fʳᶠ) = subst (Formulaᵃᵗ α ℓ) (h-map prev not) (negate fʳᶠ)
fʳᶠ→fᵃᵗ (fʳᶠ₁ ∧ fʳᶠ₂) = fʳᶠ→fᵃᵗ fʳᶠ₁ ∧ fʳᶠ→fᵃᵗ fʳᶠ₂
fʳᶠ→fᵃᵗ (fʳᶠ₁ ∨ fʳᶠ₂) = fʳᶠ→fᵃᵗ fʳᶠ₁ ∨ fʳᶠ→fᵃᵗ fʳᶠ₂
fʳᶠ→fᵃᵗ {α = α} {ℓ = ℓ} {prev = prev} (fʳᶠ₁ ⇒ fʳᶠ₂) =  subst (Formulaᵃᵗ α ℓ) (h-map prev not) (negate fʳᶠ₁) ∨ fʳᶠ→fᵃᵗ fʳᶠ₂
fʳᶠ→fᵃᵗ (∀⦗ α ⦘ fʳᶠ) = ∀⦗ α ⦘ (fʳᶠ→fᵃᵗ ∘ fʳᶠ)
fʳᶠ→fᵃᵗ (∃⦗ α ⦘ fʳᶠ) = ∃⦗ α ⦘ (fʳᶠ→fᵃᵗ ∘ fʳᶠ)
fʳᶠ→fᵃᵗ (⟨ rf ⟩ fʳᶠ) = ⟨ rf→at rf ⟩ fʳᶠ→fᵃᵗ fʳᶠ
fʳᶠ→fᵃᵗ ([ rf ] fʳᶠ) = [ rf→at rf ] fʳᶠ→fᵃᵗ fʳᶠ
fʳᶠ→fᵃᵗ (μ name ． pʳᶠ) = μ pʳᶠ→pᵃᵗ pʳᶠ
fʳᶠ→fᵃᵗ (ν name ． pʳᶠ) = ν pʳᶠ→pᵃᵗ pʳᶠ
fʳᶠ→fᵃᵗ {ℓ = ℓ} {prev = prev} ref name ⦗ args ⦘ with find prev name _≟_ | inspect (find prev name) _≟_
... | just (i , true , αs) | [ eq ]⁼ = ref cast (sym (length-map (proj₂ ∘ proj₂) prev)) i ⦗ subst (Arguments ℓ) (h-lookup prev eq) args ⦘

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
  ref_⦗_⦘ : ∀ {prev} → (i : Fin (length prev)) → Arguments ℓ (lookupᵛ (fromList prev) i) → Formulaᵃᶠ α ℓ prev

applyᵃᶠ-d : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Formulaᵃᶠ α ℓ prev
applyᵃᶠ-d (formula fᵃᶠ) = fᵃᶠ
applyᵃᶠ-d (_ ＝ t ↦ pᵃᶠ) = applyᵃᶠ-d (pᵃᶠ t)

applyᵃᶠ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Arguments ℓ params → Formulaᵃᶠ α ℓ prev
applyᵃᶠ (formula fᵃᶠ) _ = fᵃᶠ
applyᵃᶠ (_ ＝ _ ↦ pᵃᶠ) (t ∷ args) = applyᵃᶠ (pᵃᶠ t) args

ref⁺ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ (params ∷ prev)
ref⁺ fᵃᶠ = ref⁺' {prev₁ = []} fᵃᶠ
  where
  ref⁺' : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params : List (Set ℓ)} → Formulaᵃᶠ α ℓ (prev₁ ++ˡ prev₂) → Formulaᵃᶠ α ℓ (prev₁ ++ˡ params ∷ prev₂)

  ref⁺'-p : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params₁ params₂ : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ (prev₁ ++ˡ prev₂) params₁ → Parameterizedᵃᶠ α ℓ (prev₁ ++ˡ params₂ ∷ prev₂) params₁
  ref⁺'-p (formula fᵃᶠ) = formula ref⁺' fᵃᶠ
  ref⁺'-p (α ＝ a ↦ pᵃᶠ) = α ＝ a ↦ (ref⁺'-p ∘ pᵃᶠ)

  ref⁺' true = true
  ref⁺' false = false
  ref⁺' (val x) = val x
  ref⁺' (fᵃᶠ₁ ∧ fᵃᶠ₂) = ref⁺' fᵃᶠ₁ ∧ ref⁺' fᵃᶠ₂
  ref⁺' (fᵃᶠ₁ ∨ fᵃᶠ₂) = ref⁺' fᵃᶠ₁ ∨ ref⁺' fᵃᶠ₂
  ref⁺' (∀⦗ T ⦘ fᵃᶠ) = ∀⦗ T ⦘ (ref⁺' ∘ fᵃᶠ)
  ref⁺' (∃⦗ T ⦘ fᵃᶠ) = ∃⦗ T ⦘ (ref⁺' ∘ fᵃᶠ)
  ref⁺' (⟨ af ⟩ fᵃᶠ) = ⟨ af ⟩ ref⁺' fᵃᶠ
  ref⁺' ([ af ] fᵃᶠ) = [ af ] ref⁺' fᵃᶠ
  ref⁺' {prev₁ = prev₁} (μ_ {params = params} pᵃᶠ) = μ_ (ref⁺'-p {prev₁ = params ∷ prev₁} pᵃᶠ)
  ref⁺' {prev₁ = prev₁} (ν_ {params = params} pᵃᶠ) = ν_ (ref⁺'-p {prev₁ = params ∷ prev₁} pᵃᶠ)
  ref⁺' {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} {params = params} (ref i ⦗ args ⦘) with toℕ i <ᵇ length prev₁ | inspect (_<ᵇ_ (toℕ i)) (length prev₁)
  ... | false | [ eq ]⁼ = ref i' params prev₁ prev₂ i ⦗ subst (Arguments ℓ) (hlookup params prev₁ prev₂ i (≮⇒≥ λ h → subst T eq (<⇒<ᵇ h))) args ⦘
    where
    i' : {ℓ : Level} → {α : Set ℓ} → (x : α) → (xs₁ : List α) → (xs₂ : List α) → Fin (length (xs₁ ++ˡ xs₂)) → Fin (length (xs₁ ++ˡ x ∷ xs₂))
    i' _ xs₁ xs₂ i = cast (sym (trans (length-++ xs₁) (trans (+-suc (length xs₁) (length xs₂)) (cong suc (sym (length-++ xs₁)))))) (suc i)

    hlookup : {ℓ : Level} → {α : Set ℓ} → (x : α) → (xs₁ : List α) → (xs₂ : List α) → (i : Fin (length (xs₁ ++ˡ xs₂))) → toℕ i ≥ length xs₁ → lookupᵛ (fromList (xs₁ ++ˡ xs₂)) i ≡ lookupᵛ (fromList (xs₁ ++ˡ x ∷ xs₂)) (i' x xs₁ xs₂ i)
    hlookup _ [] xs₂ i _ = subst (λ j → lookupᵛ (fromList xs₂) i ≡ lookupᵛ (fromList xs₂) j) (sym (cast-is-id refl i)) refl
    hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h
  ... | true | [ eq ]⁼ = ref i' params prev₁ prev₂ i ⦗ subst (Arguments ℓ) (hlookup params prev₁ prev₂ i (<ᵇ⇒< (toℕ i) (length prev₁) (subst T (sym eq) tt₀))) args ⦘
    where
    i' : {ℓ : Level} → {α : Set ℓ} → (x : α) → (xs₁ : List α) → (xs₂ : List α) → Fin (length (xs₁ ++ˡ xs₂)) → Fin (length (xs₁ ++ˡ x ∷ xs₂))
    i' _ xs₁ xs₂ i = cast (sym (trans (length-++ xs₁) (trans (+-suc (length xs₁) (length xs₂)) (cong suc (sym (length-++ xs₁)))))) (inject₁ i)

    hlookup : {ℓ : Level} → {α : Set ℓ} → (x : α) → (xs₁ : List α) → (xs₂ : List α) → (i : Fin (length (xs₁ ++ˡ xs₂))) → toℕ i < (length xs₁) → lookupᵛ (fromList (xs₁ ++ˡ xs₂)) i ≡ lookupᵛ (fromList (xs₁ ++ˡ x ∷ xs₂)) (i' x xs₁ xs₂ i)
    hlookup _ (_ ∷ _) _ zero _ = refl
    hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h

at→af-∃ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → ActionTree α ℓ → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev
at→af-∃ ⦗ ε ⦘ fᵃᶠ = fᵃᶠ
at→af-∃ ⦗ actF af ⦘ fᵃᶠ = ⟨ af ⟩ fᵃᶠ
at→af-∃ ⦗ at * ⦘ fᵃᶠ = μ (formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ ref⁺ fᵃᶠ))
at→af-∃ (ε · at) fᵃᶠ = at→af-∃ at fᵃᶠ
at→af-∃ ((actF af) · at) fᵃᶠ = ⟨ af ⟩ at→af-∃ at fᵃᶠ
at→af-∃ ((at₁ *) · at₂) fᵃᶠ = μ (formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ ref⁺ (at→af-∃ at₂ fᵃᶠ)))
at→af-∃ (at₁ + at₂) fᵃᶠ = at→af-∃ at₁ fᵃᶠ ∨ at→af-∃ at₂ fᵃᶠ

at→af-∀ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → ActionTree α ℓ → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev
at→af-∀ ⦗ ε ⦘ fᵃᶠ = fᵃᶠ
at→af-∀ ⦗ actF af ⦘ fᵃᶠ = [ af ] fᵃᶠ
at→af-∀ ⦗ at * ⦘ fᵃᶠ = ν (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ ref⁺ fᵃᶠ))
at→af-∀ (ε · at) fᵃᶠ = at→af-∀ at fᵃᶠ
at→af-∀ ((actF af) · at) fᵃᶠ = [ af ] at→af-∀ at fᵃᶠ
at→af-∀ ((at₁ *) · at₂) fᵃᶠ = ν (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ ref⁺ (at→af-∀ at₂ fᵃᶠ)))
at→af-∀ (at₁ + at₂) fᵃᶠ = at→af-∀ at₁ fᵃᶠ ∧ at→af-∀ at₂ fᵃᶠ

fᵃᵗ→fᵃᶠ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → Formulaᵃᵗ α ℓ prev → Formulaᵃᶠ α ℓ prev

pᵃᵗ→pᵃᶠ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Parameterizedᵃᵗ α ℓ prev params → Parameterizedᵃᶠ α ℓ prev params
pᵃᵗ→pᵃᶠ (formula fᵃᵗ) = formula fᵃᵗ→fᵃᶠ fᵃᵗ
pᵃᵗ→pᵃᶠ (T ＝ t ↦ pᵃᵗ) = T ＝ t ↦ (pᵃᵗ→pᵃᶠ ∘ pᵃᵗ)

fᵃᵗ→fᵃᶠ true = true
fᵃᵗ→fᵃᶠ false = false
fᵃᵗ→fᵃᶠ (val x) = val x
fᵃᵗ→fᵃᶠ (fᵃᵗ₁ ∧ fᵃᵗ₂) = fᵃᵗ→fᵃᶠ fᵃᵗ₁ ∧ fᵃᵗ→fᵃᶠ fᵃᵗ₂
fᵃᵗ→fᵃᶠ (fᵃᵗ₁ ∨ fᵃᵗ₂) = fᵃᵗ→fᵃᶠ fᵃᵗ₁ ∨ fᵃᵗ→fᵃᶠ fᵃᵗ₂
fᵃᵗ→fᵃᶠ (∀⦗ T ⦘ fᵃᵗ) = ∀⦗ T ⦘ (fᵃᵗ→fᵃᶠ ∘ fᵃᵗ)
fᵃᵗ→fᵃᶠ (∃⦗ T ⦘ fᵃᵗ) = ∃⦗ T ⦘ (fᵃᵗ→fᵃᶠ ∘ fᵃᵗ)
fᵃᵗ→fᵃᶠ (⟨ at ⟩ fᵃᵗ) = at→af-∃ at (fᵃᵗ→fᵃᶠ fᵃᵗ)
fᵃᵗ→fᵃᶠ ([ at ] fᵃᵗ) = at→af-∀ at (fᵃᵗ→fᵃᶠ fᵃᵗ)
fᵃᵗ→fᵃᶠ (μ pᵃᵗ) = μ pᵃᵗ→pᵃᶠ pᵃᵗ
fᵃᵗ→fᵃᶠ (ν pᵃᵗ) = ν pᵃᵗ→pᵃᶠ pᵃᵗ
fᵃᵗ→fᵃᶠ ref i ⦗ args ⦘ = ref i ⦗ args ⦘

data History (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → List (List (Set ℓ)) → Set (a ⊔ sucˡ ℓ) where
  [] : ∀ {prev : List (List (Set ℓ))} → History α ℓ [] prev
  _∷_ : ∀ {prev₁ prev₂ : List (List (Set ℓ))} {params : List (Set ℓ)} → Bool × Parameterizedᵃᶠ α ℓ (params ∷ (prev₁ ++ˡ prev₂)) params → History α ℓ prev₁ prev₂ → History α ℓ (params ∷ prev₁) prev₂

lookup : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → History α ℓ prev₁ prev₂ → (i : Fin (length prev₁)) → let params = lookupᵛ (fromList prev₁) i in Bool × Σ[ prev₃ ∈ List (List (Set ℓ)) ] Parameterizedᵃᶠ α ℓ (params ∷ prev₃ ++ˡ prev₂) params × History α ℓ (params ∷ prev₃) prev₂
lookup {prev₁ = _ ∷ prev} hist@((fp , pᵃᶠ) ∷ _) zero = fp , prev , pᵃᶠ , hist
lookup (_ ∷ hist) (suc i) = lookup hist i

_++_ : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ prev₃ : List (List (Set ℓ))} → History α ℓ prev₁ (prev₂ ++ˡ prev₃) → History α ℓ prev₂ prev₃ → History α ℓ (prev₁ ++ˡ prev₂) prev₃
[] ++ hist₂ = hist₂
_++_ {α = α} {ℓ = ℓ} {prev₁ = params ∷ prev₁} {prev₂ = prev₂} {prev₃ = prev₃} ((b , pᵃᶠ) ∷ hist₁) hist₂ = (b , subst (λ x → Parameterizedᵃᶠ α ℓ (params ∷ x) params) (sym (++-assoc prev₁ prev₂ prev₃)) pᵃᶠ) ∷ (hist₁ ++ hist₂)

transform-f : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → Formulaᵃᶠ α ℓ (params ∷ prev) → Formulaᵃᶠ α ℓ (params ∷ prev ++ˡ [])
transform-f {α = α} {ℓ = ℓ} {prev = prev} {params = params} fᵃᶠ = subst (λ x → Formulaᵃᶠ α ℓ (params ∷ x)) (sym (++-identityʳ prev)) fᵃᶠ

transform-p : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params₁ params₂ : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ (params₁ ∷ prev) params₂ → Parameterizedᵃᶠ α ℓ (params₁ ∷ prev ++ˡ []) params₂
transform-p (formula fᵃᶠ) = formula transform-f fᵃᶠ
transform-p (T ＝ t ↦ pᵃᶠ) = T ＝ t ↦ (transform-p ∘ pᵃᶠ)

transform-hist : {α : Set a} → {ℓ : Level} → {prev₁ prev₂ : List (List (Set ℓ))} → {params : List (Set ℓ)} → History α ℓ (params ∷ prev₁) prev₂ → History α ℓ (params ∷ prev₁ ++ˡ []) prev₂
transform-hist {α = α} {ℓ = ℓ} {prev₁ = prev₁} {prev₂ = prev₂} {params = params} hist = subst (λ x → History α ℓ (params ∷ x) prev₂) (sym (++-identityʳ prev₁)) hist

infix 25 _⊨ᵃᶠ_⦗_⦘

_⊨ᵃᶠ_⦗_⦘ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev : List (List (Set ℓ))} → Program C R → Formulaᵃᶠ (Shape C) ℓ prev → History (Shape C) ℓ prev [] → Set (s ⊔ p ⊔ ℓ)

record Mu {C : Container s p} {R : Set r} {ℓ : Level} {prev : List (List (Set ℓ))} (x : Program C R) (f : Formulaᵃᶠ (Shape C) ℓ prev) (hist : History (Shape C) ℓ prev []) : Set (s ⊔ p ⊔ ℓ) where
  inductive
  constructor muᶜ
  field
    mu : x ⊨ᵃᶠ f ⦗ hist ⦘

record Nu {C : Container s p} {R : Set r} {ℓ : Level} {prev : List (List (Set ℓ))} (x : Program C R) (f : Formulaᵃᶠ (Shape C) ℓ prev) (hist : History (Shape C) ℓ prev []) : Set (s ⊔ p ⊔ ℓ) where
  coinductive
  constructor nuᶜ
  field
    nu : x ⊨ᵃᶠ f ⦗ hist ⦘

_ ⊨ᵃᶠ true ⦗ _ ⦘ = ⊤
_ ⊨ᵃᶠ false ⦗ _ ⦘ = ⊥
_⊨ᵃᶠ_⦗_⦘ {s = s} {p = p} {ℓ = ℓ} _ (val x) _ = Lift (s ⊔ p ⊔ ℓ) x
x ⊨ᵃᶠ fᵃᶠ₁ ∧ fᵃᶠ₂ ⦗ hist ⦘ = x ⊨ᵃᶠ fᵃᶠ₁ ⦗ hist ⦘ × x ⊨ᵃᶠ fᵃᶠ₂ ⦗ hist ⦘
x ⊨ᵃᶠ fᵃᶠ₁ ∨ fᵃᶠ₂ ⦗ hist ⦘ = x ⊨ᵃᶠ fᵃᶠ₁ ⦗ hist ⦘ ⊎ x ⊨ᵃᶠ fᵃᶠ₂ ⦗ hist ⦘
x ⊨ᵃᶠ ∀⦗ _ ⦘ fᵃᶠ ⦗ hist ⦘ = ∀ t → x ⊨ᵃᶠ fᵃᶠ t ⦗ hist ⦘
x ⊨ᵃᶠ ∃⦗ _ ⦘ fᵃᶠ ⦗ hist ⦘ = ∃[ t ] x ⊨ᵃᶠ fᵃᶠ t ⦗ hist ⦘
x ⊨ᵃᶠ ⟨ af ⟩ fᵃᶠ ⦗ hist ⦘ with free x
... | pure _ = ⊥
... | impure (s , c) = s ∈ af × ∃[ p ] c p ⊨ᵃᶠ fᵃᶠ ⦗ hist ⦘
x ⊨ᵃᶠ [ af ] fᵃᶠ ⦗ hist ⦘ with free x
... | pure _ = ⊤
... | impure (s , c) = s ∈ af → ∀ p → c p ⊨ᵃᶠ fᵃᶠ ⦗ hist ⦘
x ⊨ᵃᶠ μ pᵃᶠ ⦗ hist ⦘ = Mu x (applyᵃᶠ-d pᵃᶠ) ((false , transform-p pᵃᶠ) ∷ hist)
x ⊨ᵃᶠ ν pᵃᶠ ⦗ hist ⦘ = Nu x (applyᵃᶠ-d pᵃᶠ) ((true , transform-p pᵃᶠ) ∷ hist)
x ⊨ᵃᶠ ref i ⦗ args ⦘ ⦗ hist ⦘ with lookup hist i
... | false , _ , pᵃᶠ , hist₁ = Mu x (applyᵃᶠ pᵃᶠ args) (transform-hist hist₁)
... | true , _ , pᵃᶠ , hist₁ = Nu x (applyᵃᶠ pᵃᶠ args) (transform-hist hist₁)

infix 25 _⊨ᵃᵗ_⦗_⦘

_⊨ᵃᵗ_⦗_⦘ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev : List (List (Set ℓ))} → Program C R → Formulaᵃᵗ (Shape C) ℓ prev → History (Shape C) ℓ prev [] → Set (s ⊔ p ⊔ ℓ)
x ⊨ᵃᵗ fᵃᵗ ⦗ hist ⦘ = x ⊨ᵃᶠ fᵃᵗ→fᵃᶠ fᵃᵗ ⦗ hist ⦘

infix 25 _⊨ʳᶠ_⦗_⦘

_⊨ʳᶠ_⦗_⦘ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev : List (String × Bool × List (Set ℓ))} → Program C R → Formulaʳᶠ (Shape C) ℓ prev → History (Shape C) ℓ (map (proj₂ ∘ proj₂) prev) [] → Set (s ⊔ p ⊔ ℓ)
x ⊨ʳᶠ fʳᶠ ⦗ hist ⦘ = x ⊨ᵃᵗ fʳᶠ→fᵃᵗ fʳᶠ ⦗ hist ⦘

Formula : (α : Set a) → (ℓ : Level) → Set (a ⊔ sucˡ ℓ)
Formula α ℓ = Formulaʳᶠ α ℓ []

infix 25 _⊨_

_⊨_ : {C : Container s p} → {R : Set r} → {ℓ : Level} → Program C R → Formula (Shape C) ℓ → Set (s ⊔ p ⊔ ℓ)
x ⊨ f = x ⊨ʳᶠ f ⦗ [] ⦘
