{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerization.BaseVec where

open import Agda.Builtin.Nat using (_-_) renaming (_+_ to _＋_)
open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulasWithData using (ActionFormula; _∈_)
open import Data.Bool using (Bool)
open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; toℕ) renaming (cast to castᶠ)
open import Data.Fin.Properties using (cast-is-id)
open import Data.List using (List; map)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (+-identityʳ; suc-injective)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; head; tail) renaming (cast to castᵛ; _++_ to _++ᵛ_)
open import Function using (_∘_; id; Inverseˡ; Inverseʳ)
open import Level using (Lift; Level; _⊔_) renaming (suc to sucˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; sym; cong; cong₂; subst; subst₂)

open Bool
open Fin
open List
open Maybe
open ℕ
open Vec
open _≡_

private variable
  a s p r : Level

dropᵛ : {α : Set a} → {n : ℕ} → Vec α n → (i : Fin n) → Vec α (suc (n - suc (toℕ i)))
dropᵛ xs zero = xs
dropᵛ (_ ∷ xs) (suc i) = dropᵛ xs i

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {T params} → T → Arguments ℓ params → Arguments ℓ (T ∷ params)

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

data Formulaᵃᶠ (α : Set a) (ℓ : Level) : {n : ℕ} → Vec (List (Set ℓ)) n → Set (a ⊔ sucˡ ℓ)

data Parameterizedᵃᶠ (α : Set a) (ℓ : Level) {n : ℕ} (prev : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set (a ⊔ sucˡ ℓ) where
  formula_ : Formulaᵃᶠ α ℓ prev → Parameterizedᵃᶠ α ℓ prev []
  _＝_↦_ : ∀ {params} → (T : Set ℓ) → T → (T → Parameterizedᵃᶠ α ℓ prev params) → Parameterizedᵃᶠ α ℓ prev (T ∷ params)

data Formulaᵃᶠ α ℓ where
  true false : ∀ {n} {prev : Vec (List (Set ℓ)) n} → Formulaᵃᶠ α ℓ prev
  val_ : ∀ {n} {prev : Vec (List (Set ℓ)) n} → Set ℓ → Formulaᵃᶠ α ℓ prev
  _∧_ _∨_ : ∀ {n} {prev : Vec (List (Set ℓ)) n} → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {n} {prev : Vec (List (Set ℓ)) n} → (T : Set ℓ) → (T → Formulaᵃᶠ α ℓ prev) → Formulaᵃᶠ α ℓ prev
  ⟨_⟩_ [_]_ : ∀ {n} {prev : Vec (List (Set ℓ)) n} → ActionFormula α ℓ → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ prev
  μ_ ν_ : ∀ {n params} {prev : Vec (List (Set ℓ)) n} → Parameterizedᵃᶠ α ℓ (params ∷ prev) params → Formulaᵃᶠ α ℓ prev
  ref_⦗_⦘ : ∀ {n} {prev : Vec (List (Set ℓ)) n} → (i : Fin n) → Arguments ℓ (head (dropᵛ prev i)) → Formulaᵃᶠ α ℓ prev

applyᵃᶠ-d : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Formulaᵃᶠ α ℓ prev
applyᵃᶠ-d (formula fᵃᶠ) = fᵃᶠ
applyᵃᶠ-d (_ ＝ t ↦ pᵃᶠ) = applyᵃᶠ-d (pᵃᶠ t)

applyᵃᶠ : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Arguments ℓ params → Formulaᵃᶠ α ℓ prev
applyᵃᶠ (formula fᵃᶠ) [] = fᵃᶠ
applyᵃᶠ (_ ＝ _ ↦ pᵃᶠ) (t ∷ args) = applyᵃᶠ (pᵃᶠ t) args

data History (α : Set a) (ℓ : Level) : {n₁ n₂ : ℕ} → Vec (List (Set ℓ)) n₁ → Vec (List (Set ℓ)) n₂ → Set (a ⊔ sucˡ ℓ) where
  [] : ∀ {n} {prev : Vec (List (Set ℓ)) n} → History α ℓ [] prev
  _∷_ : ∀ {n₁ n₂ params} {prev₁ : Vec (List (Set ℓ)) n₁} {prev₂ : Vec (List (Set ℓ)) n₂} → Bool × Parameterizedᵃᶠ α ℓ (params ∷ prev₁ ++ᵛ prev₂) params → History α ℓ prev₁ prev₂ → History α ℓ (params ∷ prev₁) prev₂

drop : {α : Set a} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → History α ℓ prev₁ prev₂ → (i : Fin n₁) → History α ℓ (dropᵛ prev₁ i) prev₂
drop hist zero = hist
drop {prev₁ = _ ∷ _} (_ ∷ hist) (suc i) = drop hist i

test₁' : {ℓ : Level} → {α : Set ℓ} → {n : ℕ} → (i : Fin n) → (xs : Vec α n) → head (dropᵛ xs i) ≡ head (dropᵛ (xs ++ᵛ []) (castᶠ (sym (+-identityʳ n)) i))
test₁' zero (_ ∷ _) = refl
test₁' (suc i) (_ ∷ prev) = test₁' i prev

test₁ : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → Formulaᵃᶠ α ℓ prev → Formulaᵃᶠ α ℓ (prev ++ᵛ [])

test₁-p : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ prev params → Parameterizedᵃᶠ α ℓ (prev ++ᵛ []) params
test₁-p (formula fᵃᶠ) = formula test₁ fᵃᶠ
test₁-p (T ＝ t ↦ pᵃᶠ) = T ＝ t ↦ (test₁-p ∘ pᵃᶠ)

test₁ true = true
test₁ false = false
test₁ (val x) = val x
test₁ (fᵃᶠ₁ ∧ fᵃᶠ₂) = test₁ fᵃᶠ₁ ∧ test₁ fᵃᶠ₂
test₁ (fᵃᶠ₁ ∨ fᵃᶠ₂) = test₁ fᵃᶠ₁ ∨ test₁ fᵃᶠ₂
test₁ (∀⦗ T ⦘ fᵃᶠ) = ∀⦗ T ⦘ (test₁ ∘ fᵃᶠ)
test₁ (∃⦗ T ⦘ fᵃᶠ) = ∃⦗ T ⦘ (test₁ ∘ fᵃᶠ)
test₁ (⟨ af ⟩ fᵃᶠ) = ⟨ af ⟩ test₁ fᵃᶠ
test₁ ([ af ] fᵃᶠ) = [ af ] test₁ fᵃᶠ
test₁ (μ pᵃᶠ) = μ test₁-p pᵃᶠ
test₁ (ν pᵃᶠ) = ν test₁-p pᵃᶠ
test₁ {ℓ = ℓ} {n = n} {prev = prev} ref i ⦗ args ⦘ = ref castᶠ (sym (+-identityʳ n)) i ⦗ subst (Arguments ℓ) (test₁' i prev) args ⦘

test₂' : {ℓ : Level} → {α : Set ℓ} → {n : ℕ} → (i : Fin (n ＋ zero)) → (xs : Vec α n) → head (dropᵛ (xs ++ᵛ []) i) ≡ head (dropᵛ xs (castᶠ (+-identityʳ n) i))
test₂' zero (_ ∷ _) = refl
test₂' (suc i) (_ ∷ xs) = test₂' i xs

test₂ : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → Formulaᵃᶠ α ℓ (prev ++ᵛ []) → Formulaᵃᶠ α ℓ prev

test₂-p : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → {params : List (Set ℓ)} → Parameterizedᵃᶠ α ℓ (prev ++ᵛ []) params → Parameterizedᵃᶠ α ℓ prev params
test₂-p (formula fᵃᶠ) = formula test₂ fᵃᶠ
test₂-p (T ＝ t ↦ pᵃᶠ) = T ＝ t ↦ (test₂-p ∘ pᵃᶠ)

test₂ true = true
test₂ false = false
test₂ (val x) = val x
test₂ (fᵃᶠ₁ ∧ fᵃᶠ₂) = test₂ fᵃᶠ₁ ∧ test₂ fᵃᶠ₂
test₂ (fᵃᶠ₁ ∨ fᵃᶠ₂) = test₂ fᵃᶠ₁ ∨ test₂ fᵃᶠ₂
test₂ (∀⦗ T ⦘ fᵃᶠ) = ∀⦗ T ⦘ (test₂ ∘ fᵃᶠ)
test₂ (∃⦗ T ⦘ fᵃᶠ) = ∃⦗ T ⦘ (test₂ ∘ fᵃᶠ)
test₂ (⟨ af ⟩ fᵃᶠ) = ⟨ af ⟩ test₂ fᵃᶠ
test₂ ([ af ] fᵃᶠ) = [ af ] test₂ fᵃᶠ
test₂ (μ pᵃᶠ) = μ test₂-p pᵃᶠ
test₂ (ν pᵃᶠ) = ν test₂-p pᵃᶠ
test₂ {ℓ = ℓ} {n = n} {prev = prev} ref i ⦗ args ⦘ = ref castᶠ (+-identityʳ n) i ⦗ subst (Arguments ℓ) (test₂' i prev) args ⦘

_++'_ : {α : Set a} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → History α ℓ prev₁ prev₂ → History α ℓ prev₂ [] → History α ℓ (prev₁ ++ᵛ prev₂) []
[] ++' hist₂ = hist₂
_++'_ {α = α} {ℓ = ℓ} {prev₁ = params ∷ prev₁} {prev₂ = prev₂} ((flag , pᵃᶠ) ∷ hist₁) hist₂ = (flag , test₁-p pᵃᶠ) ∷ (hist₁ ++' hist₂)

infix 25 _⊨ᵃᶠ_｛_｝

_⊨ᵃᶠ_｛_｝ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → Program C R → Formulaᵃᶠ (Shape C) ℓ prev → History (Shape C) ℓ prev [] → Set (s ⊔ p ⊔ ℓ)

record Mu {C : Container s p} {R : Set r} {ℓ : Level} {n : ℕ} {prev : Vec (List (Set ℓ)) n} (x : Program C R) (f : Formulaᵃᶠ (Shape C) ℓ prev) (hist : History (Shape C) ℓ prev []) : Set (s ⊔ p ⊔ ℓ) where
  inductive
  constructor muᶜ
  field
    mu : x ⊨ᵃᶠ f ｛ hist ｝

record Nu {C : Container s p} {R : Set r} {ℓ : Level} {n : ℕ} {prev : Vec (List (Set ℓ)) n} (x : Program C R) (f : Formulaᵃᶠ (Shape C) ℓ prev) (hist : History (Shape C) ℓ prev []) : Set (s ⊔ p ⊔ ℓ) where
  coinductive
  constructor nuᶜ
  field
    nu : x ⊨ᵃᶠ f ｛ hist ｝

_⊨ᵃᶠ'_｛_｝ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) (suc n)} → (x : Program C R) → Arguments ℓ (head prev) → History (Shape C) ℓ prev [] → Set (s ⊔ p ⊔ ℓ)
x ⊨ᵃᶠ' args ｛ hist@((false , pᵃᶠ) ∷ _) ｝ = Mu x (applyᵃᶠ (test₂-p pᵃᶠ) args) hist
x ⊨ᵃᶠ' args ｛ hist@((true , pᵃᶠ) ∷ _) ｝ = Nu x (applyᵃᶠ (test₂-p pᵃᶠ) args) hist

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
_⊨ᵃᶠ_｛_｝ {C = C} {ℓ = ℓ} {prev = prev} x (μ_ {params = params} pᵃᶠ) hist = Mu x (applyᵃᶠ-d pᵃᶠ) ((false , test₁-p pᵃᶠ) ∷ hist)
_⊨ᵃᶠ_｛_｝ {C = C} {ℓ = ℓ} {prev = prev} x (ν_ {params = params} pᵃᶠ) hist = Nu x (applyᵃᶠ-d pᵃᶠ) ((true , test₁-p pᵃᶠ) ∷ hist)
x ⊨ᵃᶠ ref i ⦗ args ⦘ ｛ hist ｝ = x ⊨ᵃᶠ' args ｛ drop hist i ｝

-- proof : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → (fᵃᶠ : Formulaᵃᶠ α ℓ prev) → (test₂ (test₁ fᵃᶠ)) ≡ fᵃᶠ

-- proof-p : {α : Set a} → {ℓ : Level} → {n : ℕ} → {prev : Vec (List (Set ℓ)) n} → {params : List (Set ℓ)} → (pᵃᶠ : Parameterizedᵃᶠ α ℓ (params ∷ prev) params) → (test₂-p ∘ test₁-p) pᵃᶠ ≡ pᵃᶠ
-- proof-p (formula fᵃᶠ) = cong formula_ (proof fᵃᶠ)
-- proof-p (T ＝ t ↦ pᵃᶠ) = cong (_＝_↦_ T t) {! _≗_ (test₂-p ∘ test₁-p ∘ pᵃᶠ) pᵃᶠ  !}

-- proof true = refl
-- proof false = refl
-- proof (val x) = refl
-- proof (fᵃᶠ₁ ∧ fᵃᶠ₂) = cong₂ _∧_ (proof fᵃᶠ₁) (proof fᵃᶠ₂)
-- proof (fᵃᶠ₁ ∨ fᵃᶠ₂) = cong₂ _∨_ (proof fᵃᶠ₁) (proof fᵃᶠ₂)
-- proof (∀⦗ T ⦘ fᵃᶠ) = cong (∀⦗_⦘_ T) {!   !}
-- proof (∃⦗ T ⦘ fᵃᶠ) = cong (∃⦗_⦘_ T) {!   !}
-- proof (⟨ af ⟩ fᵃᶠ) = cong (⟨_⟩_ af) (proof fᵃᶠ)
-- proof ([ af ] fᵃᶠ) = cong ([_]_ af) (proof fᵃᶠ)
-- proof (μ pᵃᶠ) = cong μ_ (proof-p pᵃᶠ)
-- proof (ν pᵃᶠ) = cong ν_ (proof-p pᵃᶠ)
-- proof ref i ⦗ args ⦘ = {!   !}

open import Agda.Builtin.Nat using () renaming (_+_ to _＋_)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.List using (length) renaming (_++_ to _++ˡ_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (_<_; _>_; z<s; s<s; _<?_) -- renaming (_≟_ to _≟ⁿ_)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n; ≮⇒≥)
open import Relation.Binary.PropositionalEquality using (_≢_; inspect; trans) renaming ([_] to [_]⁼)
open import Relation.Nullary using (no; yes)

open Mu
open Nu
open _⊎_

h-drop-≡ : {α : Set a} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → {params : List (Set ℓ)} → (i : Fin (n₁ ＋ suc n₂)) → (hist₁ : History α ℓ prev₁ (params ∷ prev₂)) → (hist₂ : History α ℓ prev₂ []) → (flag : Bool) → (pᵃᶠ : Parameterizedᵃᶠ α ℓ (params ∷ prev₂ ++ᵛ []) params) → (h : toℕ i ≡ n₁) → drop (hist₁ ++' ((flag , pᵃᶠ) ∷ hist₂)) i ≡ {!   !} -- {! cast-hist ? ((flag , pᵃᶠ) ∷ hist₂)  !}
h-drop-≡ i hist₁ hist₂ flag pᵃᶠ h = {!   !}

h-drop-< : {α : Set a} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → {params : List (Set ℓ)} → (i : Fin (n₁ ＋ suc n₂)) → (hist₁ : History α ℓ prev₁ (params ∷ prev₂)) → (hist₂ : History α ℓ prev₂ []) → (flag₁ flag₂ : Bool) → (pᵃᶠ₁ pᵃᶠ₂ : Parameterizedᵃᶠ α ℓ (params ∷ prev₂ ++ᵛ []) params) → (h : toℕ i > n₁) → drop (hist₁ ++' ((flag₁ , pᵃᶠ₁) ∷ hist₂)) i ≡ drop (hist₁ ++' ((flag₂ , pᵃᶠ₂) ∷ hist₂)) i
h-drop-< (suc _) [] _ _ _ _ _ _ = refl
h-drop-< (suc i) (_ ∷ hist₁) hist₂ flag₁ flag₂ pᵃᶠ₁ pᵃᶠ₂ (s<s h) = h-drop-< i hist₁ hist₂ flag₁ flag₂ pᵃᶠ₁ pᵃᶠ₂ h

subst-prev : {C : Container s p} → {R : Set r} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → (x : Program C R) → (fᵃᶠ : Formulaᵃᶠ (Shape C) ℓ (prev₁ ++ᵛ [] ∷ prev₂)) → (flag : Bool) → (fᵃᶠ₁ fᵃᶠ₂ : Formulaᵃᶠ (Shape C) ℓ ([] ∷ prev₂)) → (hist₁ : History (Shape C) ℓ prev₁ ([] ∷ prev₂)) → (hist₂ : History (Shape C) ℓ prev₂ []) → ((x' : Program C R) → x' ⊨ᵃᶠ fᵃᶠ₁ ｛ (flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂ ｝ → x' ⊨ᵃᶠ fᵃᶠ₂ ｛ (flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂ ｝) → x ⊨ᵃᶠ fᵃᶠ ｛ hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂) ｝ → x ⊨ᵃᶠ fᵃᶠ ｛ hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₂)) ∷ hist₂) ｝

subst-prev-pᵈ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → {params : List (Set ℓ)} → (x : Program C R) → (pᵃᶠ : Parameterizedᵃᶠ (Shape C) ℓ (prev₁ ++ᵛ [] ∷ prev₂) params) → (flag : Bool) → (fᵃᶠ₁ fᵃᶠ₂ : Formulaᵃᶠ (Shape C) ℓ ([] ∷ prev₂)) → (hist₁ : History (Shape C) ℓ prev₁ ([] ∷ prev₂)) → (hist₂ : History (Shape C) ℓ prev₂ []) → ((x' : Program C R) → x' ⊨ᵃᶠ fᵃᶠ₁ ｛ (flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂ ｝ → x' ⊨ᵃᶠ fᵃᶠ₂ ｛ (flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂ ｝) → x ⊨ᵃᶠ applyᵃᶠ-d pᵃᶠ ｛ hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂) ｝ → x ⊨ᵃᶠ applyᵃᶠ-d pᵃᶠ ｛ hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₂)) ∷ hist₂) ｝
subst-prev-pᵈ x (formula fᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h = subst-prev x fᵃᶠ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h
subst-prev-pᵈ x (_ ＝ t ↦ pᵃᶠ) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h = subst-prev-pᵈ x (pᵃᶠ t) flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h

subst-prev-p : {C : Container s p} → {R : Set r} → {ℓ : Level} → {n₁ n₂ : ℕ} → {prev₁ : Vec (List (Set ℓ)) n₁} → {prev₂ : Vec (List (Set ℓ)) n₂} → {params : List (Set ℓ)} → (x : Program C R) → (pᵃᶠ : Parameterizedᵃᶠ (Shape C) ℓ (prev₁ ++ᵛ [] ∷ prev₂) params) → (args : Arguments ℓ params) → (flag : Bool) → (fᵃᶠ₁ fᵃᶠ₂ : Formulaᵃᶠ (Shape C) ℓ ([] ∷ prev₂)) → (hist₁ : History (Shape C) ℓ prev₁ ([] ∷ prev₂)) → (hist₂ : History (Shape C) ℓ prev₂ []) → ((x' : Program C R) → x' ⊨ᵃᶠ fᵃᶠ₁ ｛ (flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂ ｝ → x' ⊨ᵃᶠ fᵃᶠ₂ ｛ (flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂ ｝) → x ⊨ᵃᶠ applyᵃᶠ pᵃᶠ args ｛ hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂) ｝ → x ⊨ᵃᶠ applyᵃᶠ pᵃᶠ args ｛ hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₂)) ∷ hist₂) ｝
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
subst-prev {n₁ = n₁} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h with drop (hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂)) i | inspect (drop (hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₁)) ∷ hist₂))) i | drop (hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₂)) ∷ hist₂)) i | inspect (drop (hist₁ ++' ((flag , test₁-p (formula fᵃᶠ₂)) ∷ hist₂))) i
... | drop₁ | [ eq₁ ]⁼ | drop₂ | [ eq₂ ]⁼ with n₁ <? (toℕ i)
...   | yes h< with trans (sym eq₁) (trans (h-drop-< i hist₁ hist₂ flag flag (test₁-p (formula fᵃᶠ₁)) (test₁-p (formula fᵃᶠ₂)) h<) eq₂)
... | refl = h
subst-prev {n₁ = n₁} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | drop₁ | [ eq₁ ]⁼ | drop₂ | [ eq₂ ]⁼ | no h≮ with m≤n⇒m<n∨m≡n (≮⇒≥ h≮)
... | inj₂ h≡ = {!   !}
subst-prev {n₁ = n₁} x ref i ⦗ args ⦘ flag fᵃᶠ₁ fᵃᶠ₂ hist₁ hist₂ h→ h | drop₁ | [ eq₁ ]⁼ | drop₂ | [ eq₂ ]⁼ | no h≮ | inj₁ h> = {!   !}
