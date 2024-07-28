{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.FixedPoints.Base where

open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulas using (ActionFormula; _∈_)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; _≟_; _↑ˡ_; fromℕ<; inject₁)
open import Data.List using (List; length; findIndexᵇ; lookup)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷⁺_; foldr; toList) renaming (length to length⁺; map to map⁺)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _<′_; ≤′-refl; _+_)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Nat.Properties using (+-suc; m≤n⇒m≤n+o; n<1+n; +-identityʳ; +-assoc)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.String using (String; _==_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; _++_) renaming (map to mapᵛ; lookup to lookupᵛ)
open import Induction.WellFounded using (WellFounded; Acc)
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Nullary using (¬_; yes; no)

open Bool
open Container
open Fin
open List
open ℕ
open Vec
open Acc

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

data Maybe' (α : Set ℓ) : Set ℓ where
  val_ : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

data Result (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  res_ : Maybe' (Program C α × Fin n) → Result C α n
  _×∃_ : ∀ {s} → ActionFormula (Shape C) → (Position C s → Result C α n) → Result C α n
  _×∀_ : ∀ {s} → ActionFormula (Shape C) → (Position C s → Result C α n) → Result C α n

unfold : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Result C α n → Maybe' (Program C α × Fin n) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold (res v) o x = o ≡ v → x
unfold (_×∃_ {s = s} af c) o x = s ∈ af × ∃[ p ] unfold (c p) o x
unfold (_×∀_ {s = s} af c) o x = s ∈ af → ∀ p → unfold (c p) o x

_<_ : {α : Set ℓ} → Rel (List⁺ α) 0ℓ
xs < ys = length⁺ xs <′ length⁺ ys

<-wf : {α : Set ℓ} → WellFounded (_<_ {α = α})
<-wf xs = acc<′⇒acc< (<′-wellFounded (length⁺ xs))
  where
    acc<′⇒acc< : {α : Set ℓ} → {xs : List⁺ α} → Acc _<′_ (length⁺ xs) → Acc _<_ xs
    acc<′⇒acc< (acc h) = acc λ hlt → acc<′⇒acc< (h hlt)

unfold⁺ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → (rs : List⁺ (Result C α n)) → Acc _<_ rs → Maybe' (Program C α × Fin n) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold⁺ (r ∷ []) _ o x = unfold r o x
unfold⁺ (r₁ ∷ r₂ ∷ rs) (acc h) o x = unfold r₁ o x × unfold⁺ (r₂ ∷ rs) (h ≤′-refl) o x

record Containerⁱ (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shapeⁱ : ℕ
    Positionⁱ : Fin Shapeⁱ → Program C α → List⁺ (Result C α n)

open Containerⁱ

extend : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Vec (FixedPoint × Containerⁱ C α (suc n)) (suc n) → (Maybe' (Program C α × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' (Program C α × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Maybe' (Program C α × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
extend xs mu nu (val (x , i)) with lookupᵛ xs i
... | leastFP , (S ▷ P) = ∃[ s ] ∀ {o} → let rs = P s x in unfold⁺ rs (<-wf rs) o (mu o)
... | greatestFP , (S ▷ P) = ∃[ s ] ∀ {o} → let rs = P s x in unfold⁺ rs (<-wf rs) o (nu o)
extend _ _ _ done = ⊤
extend _ _ _ fail = ⊥

record Mu {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × Containerⁱ C α (suc n)) (suc n)) (_ : Maybe' (Program C α × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record Nu {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × Containerⁱ C α (suc n)) (suc n)) (_ : Maybe' (Program C α × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record Mu xs i where
  inductive
  constructor muᶜ
  field
    mu : extend xs (Mu xs) (Nu xs) i

record Nu xs i where
  coinductive
  constructor nuᶜ
  field
    nu : extend xs (Mu xs) (Nu xs) i

infix 60 refⁱ_
infix 55 ~ⁱ_
infix 50 ⟨_⟩ⁱ_
infix 50 [_]ⁱ_
infixr 45 _∧ⁱ_
infixr 40 _∨ⁱ_
infixr 35 _⇒ⁱ_
infix 30 μⁱ_
infix 30 νⁱ_

data Formulaⁱ (S : Set ℓ) : ℕ → Set ℓ where
  trueⁱ falseⁱ : ∀ {n} → Formulaⁱ S n
  ~ⁱ_ : ∀ {n} → Formulaⁱ S n → Formulaⁱ S n
  _∧ⁱ_ _∨ⁱ_ _⇒ⁱ_ : ∀ {n} → Formulaⁱ S n → Formulaⁱ S n → Formulaⁱ S n
  ⟨_⟩ⁱ_ [_]ⁱ_ : ∀ {n} → ActionFormula S → Formulaⁱ S n → Formulaⁱ S n
  μⁱ_ νⁱ_ : ∀ {n} → Formulaⁱ S (suc n) → Formulaⁱ S n
  refⁱ_ : ∀ {n} → Fin n → Formulaⁱ S n

infix 25 _⊨ⁱ_

_⊨ⁱ_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formulaⁱ (Shape C) zero → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
x ⊨ⁱ fⁱ = x ⊨ᵈ f'→fᵈⁿᶠ (fⁱ→f' fⁱ)
  where
  infix 60 ref'〔_〕_
  infix 50 ⟨_⟩'_
  infix 50 [_]'_
  infixr 45 _∧'_
  infixr 40 _∨'_
  infix 30 μ'_
  infix 30 ν'_

  data Formula' (S : Set ℓ) : ℕ → Set ℓ where
    true' false' : ∀ {n} → Formula' S n
    _∧'_ _∨'_ : ∀ {n} → Formula' S n → Formula' S n → Formula' S n
    ⟨_⟩'_ [_]'_ : ∀ {n} → ActionFormula S → Formula' S n → Formula' S n
    μ'_ ν'_ : ∀ {n} → Formula' S (suc n) → Formula' S n
    ref'〔_〕_ : ∀ {n} → Bool → Fin n → Formula' S n

  flipRef : {S : Set ℓ} → {n : ℕ} → Fin n → Formula' S n → Formula' S n
  flipRef _ true' = true'
  flipRef _ false' = false'
  flipRef x (f'₁ ∧' f'₂) = flipRef x f'₁ ∧' flipRef x f'₂
  flipRef x (f'₁ ∨' f'₂) = flipRef x f'₁ ∨' flipRef x f'₂
  flipRef x (⟨ af ⟩' f') = ⟨ af ⟩' flipRef x f'
  flipRef x ([ af ]' f') = [ af ]' flipRef x f'
  flipRef x (μ' f') = μ' flipRef (suc x) f'
  flipRef x (ν' f') = ν' flipRef (suc x) f'
  flipRef x (ref'〔 b 〕 i) with i ≟ x
  ... | no _ = ref'〔 b 〕 i
  ... | yes _ = ref'〔 not b 〕 i

  negate : {S : Set ℓ} → {n : ℕ} → Formula' S n → Formula' S n
  negate true' = false'
  negate false' = true'
  negate (f'₁ ∧' f'₂) = negate f'₁ ∨' negate f'₂
  negate (f'₁ ∨' f'₂) = negate f'₁ ∧' negate f'₂
  negate (⟨ af ⟩' f') = [ af ]' negate f'
  negate ([ af ]' f') = ⟨ af ⟩' negate f'
  negate (μ' f') = ν' flipRef zero (negate f')
  negate (ν' f') = μ' flipRef zero (negate f')
  negate (ref'〔 b 〕 i) = ref'〔 not b 〕 i

  fⁱ→f' : {S : Set ℓ} → {n : ℕ} → Formulaⁱ S n → Formula' S n
  fⁱ→f' trueⁱ = true'
  fⁱ→f' falseⁱ = false'
  fⁱ→f' (~ⁱ fⁱ) = negate (fⁱ→f' fⁱ)
  fⁱ→f' (fⁱ₁ ∧ⁱ fⁱ₂) = fⁱ→f' fⁱ₁ ∧' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ∨ⁱ fⁱ₂) = fⁱ→f' fⁱ₁ ∨' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ⇒ⁱ fⁱ₂) = negate (fⁱ→f' fⁱ₁) ∨' fⁱ→f' fⁱ₂
  fⁱ→f' (⟨ af ⟩ⁱ fⁱ) = ⟨ af ⟩' fⁱ→f' fⁱ
  fⁱ→f' ([ af ]ⁱ fⁱ) = [ af ]' fⁱ→f' fⁱ
  fⁱ→f' (μⁱ fⁱ) = μ' fⁱ→f' fⁱ
  fⁱ→f' (νⁱ fⁱ) = ν' fⁱ→f' fⁱ
  fⁱ→f' (refⁱ i) = ref'〔 true 〕 i

  data Formulaᵈⁿᶠ-var (S : Set ℓ) : ℕ → Set ℓ
  data Formulaᵈⁿᶠ-con (S : Set ℓ) : ℕ → Set ℓ
  data Formulaᵈⁿᶠ-dis (S : Set ℓ) : ℕ → Set ℓ

  infix 60 refᵈⁿᶠ_
  infix 55 ⟨_⟩ᵈⁿᶠ_
  infix 55 [_]ᵈⁿᶠ_
  infix 50 μᵈⁿᶠ_
  infix 50 νᵈⁿᶠ_

  data Formulaᵈⁿᶠ-var S where
    trueᵈⁿᶠ falseᵈⁿᶠ : ∀ {n} → Formulaᵈⁿᶠ-var S n
    ⟨_⟩ᵈⁿᶠ_ [_]ᵈⁿᶠ_ : ∀ {n} → ActionFormula S → Formulaᵈⁿᶠ-var S n → Formulaᵈⁿᶠ-var S n
    μᵈⁿᶠ_ νᵈⁿᶠ_ : ∀ {n} → Formulaᵈⁿᶠ-dis S (suc n) → Formulaᵈⁿᶠ-var S n
    refᵈⁿᶠ_ : ∀ {n} → Fin n → Formulaᵈⁿᶠ-var S n

  infix 45 con-var_
  infixr 40 _∧ᵈⁿᶠ_

  data Formulaᵈⁿᶠ-con S where
    con-var_ : ∀ {n} → Formulaᵈⁿᶠ-var S n → Formulaᵈⁿᶠ-con S n
    _∧ᵈⁿᶠ_ : ∀ {n} → Formulaᵈⁿᶠ-var S n → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-con S n

  infix 35 dis-con_
  infixr 30 _∨ᵈⁿᶠ_

  data Formulaᵈⁿᶠ-dis S where
    dis-con_ : ∀ {n} → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-dis S n
    _∨ᵈⁿᶠ_ : ∀ {n} → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n

  merge-dis-dis-or : {S : Set ℓ} → {n : ℕ} → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n
  merge-dis-dis-or (dis-con c) d = c ∨ᵈⁿᶠ d
  merge-dis-dis-or (c ∨ᵈⁿᶠ d₁) d₂ = c ∨ᵈⁿᶠ merge-dis-dis-or d₁ d₂

  merge-con-con : {S : Set ℓ} → {n : ℕ} → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-con S n
  merge-con-con (con-var v) c = v ∧ᵈⁿᶠ c
  merge-con-con (v ∧ᵈⁿᶠ c₁) c₂ = v ∧ᵈⁿᶠ merge-con-con c₁ c₂

  merge-con-dis : {S : Set ℓ} → {n : ℕ} → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n
  merge-con-dis c₁ (dis-con c₂) = dis-con (merge-con-con c₁ c₂)
  merge-con-dis c₁ (c₂ ∨ᵈⁿᶠ d₂) = merge-con-con c₁ c₂ ∨ᵈⁿᶠ merge-con-dis c₁ d₂

  merge-dis-dis-and : {S : Set ℓ} → {n : ℕ} → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n
  merge-dis-dis-and (dis-con c) d = merge-con-dis c d
  merge-dis-dis-and (c ∨ᵈⁿᶠ d₁) d₂ = merge-dis-dis-or (merge-con-dis c d₂) (merge-dis-dis-and d₁ d₂)

  f'→fᵈⁿᶠ : {S : Set ℓ} → {n : ℕ} → Formula' S n → Formulaᵈⁿᶠ-dis S n
  f'→fᵈⁿᶠ true' = dis-con (con-var trueᵈⁿᶠ)
  f'→fᵈⁿᶠ false' = dis-con (con-var falseᵈⁿᶠ)
  f'→fᵈⁿᶠ (f'₁ ∧' f'₂) = merge-dis-dis-and (f'→fᵈⁿᶠ f'₁) (f'→fᵈⁿᶠ f'₂)
  f'→fᵈⁿᶠ (f'₁ ∨' f'₂) = merge-dis-dis-or (f'→fᵈⁿᶠ f'₁) (f'→fᵈⁿᶠ f'₂)
  f'→fᵈⁿᶠ (⟨ af ⟩' f') = merge-∃-dis af (f'→fᵈⁿᶠ f')
    where
    merge-∃-var : {S : Set ℓ} → {n : ℕ} → ActionFormula S → Formulaᵈⁿᶠ-var S n → Formulaᵈⁿᶠ-var S n
    merge-∃-var af v = ⟨ af ⟩ᵈⁿᶠ v

    merge-∃-con : {S : Set ℓ} → {n : ℕ} → ActionFormula S → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-con S n
    merge-∃-con af (con-var v) = con-var (merge-∃-var af v)
    merge-∃-con af (v ∧ᵈⁿᶠ c) = merge-∃-var af v ∧ᵈⁿᶠ merge-∃-con af c

    merge-∃-dis : {S : Set ℓ} → {n : ℕ} → ActionFormula S → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n
    merge-∃-dis af (dis-con c) = dis-con (merge-∃-con af c)
    merge-∃-dis af (c ∨ᵈⁿᶠ d) = merge-∃-con af c ∨ᵈⁿᶠ merge-∃-dis af d
  f'→fᵈⁿᶠ ([ af ]' f') = merge-∀-dis af (f'→fᵈⁿᶠ f')
    where
    merge-∀-var : {S : Set ℓ} → {n : ℕ} → ActionFormula S → Formulaᵈⁿᶠ-var S n → Formulaᵈⁿᶠ-var S n
    merge-∀-var af v = [ af ]ᵈⁿᶠ v

    merge-∀-con : {S : Set ℓ} → {n : ℕ} → ActionFormula S → Formulaᵈⁿᶠ-con S n → Formulaᵈⁿᶠ-con S n
    merge-∀-con af (con-var v) = con-var (merge-∀-var af v)
    merge-∀-con af (v ∧ᵈⁿᶠ c) = merge-∀-var af v ∧ᵈⁿᶠ merge-∀-con af c

    merge-∀-dis : {S : Set ℓ} → {n : ℕ} → ActionFormula S → Formulaᵈⁿᶠ-dis S n → Formulaᵈⁿᶠ-dis S n
    merge-∀-dis af (dis-con c) = dis-con (merge-∀-con af c)
    merge-∀-dis af (c ∨ᵈⁿᶠ d) = merge-∀-con af c ∨ᵈⁿᶠ merge-∀-dis af d
  f'→fᵈⁿᶠ (μ' f') = dis-con (con-var (μᵈⁿᶠ f'→fᵈⁿᶠ f'))
  f'→fᵈⁿᶠ (ν' f') = dis-con (con-var (νᵈⁿᶠ f'→fᵈⁿᶠ f'))
  f'→fᵈⁿᶠ (ref'〔 false 〕 _) = dis-con con-var falseᵈⁿᶠ
  f'→fᵈⁿᶠ (ref'〔 true 〕 i) = dis-con (con-var (refᵈⁿᶠ i))

  _↑_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Containerⁱ C α n → (x : ℕ) → Containerⁱ C α (n + x)
  Shapeⁱ ((S ▷ _) ↑ _) = S
  Positionⁱ ((S ▷ P) ↑ n) s i with P s i
  ... | xs = map⁺ (λ x → x ↑' n) xs
    where
    _↑'_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Result C α n → (x : ℕ) → Result C α (n + x)
    (res (val (fst , snd))) ↑' x = res (val (fst , snd ↑ˡ x))
    (res done) ↑' _ = res done
    (res fail) ↑' _ = res fail
    (af ×∃ c) ↑' n = af ×∃ λ p → (c p) ↑' n
    (af ×∀ c) ↑' n = af ×∀ λ p → (c p) ↑' n

  data ModalitySequence (S : Set ℓ) : Set ℓ where
    ⟪_⟫_ ⟦_⟧_ : ActionFormula S → ModalitySequence S → ModalitySequence S
    ε : ModalitySequence S

  apply : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → ModalitySequence (Shape C) → Program C α → (Maybe' (Program C α) → Result C α n) → Result C α n
  apply (⟪ af ⟫ m) x f with free x
  ... | pure _ = f fail
  ... | impure (_ , c) = af ×∃ λ p → apply m (c p) f
  apply (⟦ af ⟧ m) x f with free x
  ... | pure _ = f done
  ... | impure (_ , c) = af ×∀ λ p → apply m (c p) f
  apply ε x f = f (val x)

  containerize-var : {n n₁ : ℕ} → (C : Container ℓ₁ ℓ₂) → (α : Set ℓ₃) → Formulaᵈⁿᶠ-var (Shape C) (suc n) → Vec (Fin (suc n₁)) (suc n) → ModalitySequence (Shape C) × Maybe' (∃[ n₂ ] (Fin (suc n₁ + n₂)) × Vec (FixedPoint × Containerⁱ C α (suc n₁ + n₂)) n₂)
  containerize-con : {n n₁ : ℕ} → (C : Container ℓ₁ ℓ₂) → (α : Set ℓ₃) → Formulaᵈⁿᶠ-con (Shape C) (suc n) → Vec (Fin (suc n₁)) (suc n) → ∃[ n₂ ] List⁺ (ModalitySequence (Shape C) × Maybe' (Fin (suc n₁ + n₂))) × Vec (FixedPoint × Containerⁱ C α (suc n₁ + n₂)) n₂
  containerize-dis : {n n₁ : ℕ} → (C : Container ℓ₁ ℓ₂) → (α : Set ℓ₃) → Formulaᵈⁿᶠ-dis (Shape C) (suc n) → Vec (Fin (suc n₁)) (suc n) → ∃[ n₂ ] List⁺ (List⁺ (ModalitySequence (Shape C) × Maybe' (Fin (suc n₁ + n₂)))) × Vec (FixedPoint × Containerⁱ C α (suc n₁ + n₂)) n₂
  containerize : {n n₁ : ℕ} → (C : Container ℓ₁ ℓ₂) → (α : Set ℓ₃) → FixedPoint → Formulaᵈⁿᶠ-dis (Shape C) (suc n) → Vec (Fin n₁) n → ∃[ n₂ ] Vec (FixedPoint × Containerⁱ C α (n₁ + suc n₂)) (suc n₂)

  containerize-var _ _ trueᵈⁿᶠ _ = ε , done
  containerize-var _ _ falseᵈⁿᶠ _ = ε , fail
  containerize-var C α (⟨ af ⟩ᵈⁿᶠ v) prev with containerize-var C α v prev
  ... | m , x = ⟪ af ⟫ m , x
  containerize-var C α ([ af ]ᵈⁿᶠ v) prev with containerize-var C α v prev
  ... | m , x = ⟦ af ⟧ m , x
  containerize-var {n₁ = n₁} C α (μᵈⁿᶠ d) prev with containerize C α leastFP d prev
  ... | n₂ , Cs = ε , val (suc n₂ , subst Fin (sym (+-suc (suc n₁) n₂)) (fromℕ< (m≤n⇒m≤n+o n₂ (n<1+n (suc n₁)))) , Cs)
  containerize-var {n₁ = n₁} C α (νᵈⁿᶠ d) prev with containerize C α greatestFP d prev
  ... | n₂ , Cs = ε , val (suc n₂ , subst Fin (sym (+-suc (suc n₁) n₂)) (fromℕ< (m≤n⇒m≤n+o n₂ (n<1+n (suc n₁)))) , Cs)
  containerize-var {n₁ = n₁} _ _ (refᵈⁿᶠ i) prev = ε , val (zero , subst Fin (sym (+-identityʳ (suc n₁))) (lookupᵛ prev i) , [])

  containerize-con C α (con-var v) prev with containerize-var C α v prev
  ... | m , val (n₂ , i , Cs) = n₂ , [ m , val i ] , Cs
  ... | m , done = zero , [ m , done ] , []
  ... | m , fail = zero , [ m , fail ] , []
  containerize-con C α (v ∧ᵈⁿᶠ c) prev with containerize-var C α v prev
  containerize-con {n₁ = n₁} C α (v ∧ᵈⁿᶠ c) prev | m , val (n₂ , _ , Cs₁) with containerize-con C α c (mapᵛ (λ x → x ↑ˡ n₂) prev)
  ... | n₃ , xs , Cs₂ = n₂ + n₃ , subst (λ n → List⁺ (ModalitySequence (Shape C) × Maybe' (Fin n)) × Vec (FixedPoint × Containerⁱ C α n) (n₂ + n₃)) (+-assoc (suc n₁) n₂ n₃) ((m , val (fromℕ< (m≤n⇒m≤n+o n₃ (n<1+n (n₁ + n₂))))) ∷⁺ xs , mapᵛ (λ (fp , C) → fp , (C ↑ n₃)) Cs₁ ++ Cs₂)
  containerize-con C α (v ∧ᵈⁿᶠ c) prev | m , done with containerize-con C α c prev
  ... | n₂ , xs , Cs = n₂ , (m , done) ∷⁺ xs , Cs
  containerize-con C α (v ∧ᵈⁿᶠ c) prev | m , fail with containerize-con C α c prev
  ... | n₂ , xs , Cs = n₂ , (m , fail) ∷⁺ xs , Cs

  containerize-dis C α (dis-con c) prev with containerize-con C α c prev
  ... | n₂ , x , Cs = n₂ , [ x ] , Cs
  containerize-dis {n₁ = n₁} C α (c ∨ᵈⁿᶠ d) prev with containerize-con C α c prev
  ... | n₂ , x , Cs₁ with containerize-dis C α d (mapᵛ (λ x → x ↑ˡ n₂) prev)
  ...   | n₃ , xs , Cs₂ = n₂ + n₃ , subst (λ n → List⁺ (List⁺ (ModalitySequence (Shape C) × Maybe' (Fin n))) × Vec (FixedPoint × Containerⁱ C α n) (n₂ + n₃)) (+-assoc (suc n₁) n₂ n₃) (map⁺ (λ { (m , val x) → m , val (x ↑ˡ n₃) ; (m , done) → m , done ; (m , fail) → m , fail }) x ∷⁺ xs , mapᵛ (λ (fp , C) → fp , (C ↑ n₃)) Cs₁ ++ Cs₂)

  containerize {n₁ = n₁} C α fp d prev with containerize-dis C α d (fromℕ< (n<1+n n₁) ∷ mapᵛ inject₁ prev)
  ... | n₂ , xs , Cs = n₂ , subst (λ n → Vec (FixedPoint × Containerⁱ C α n) (suc n₂)) (sym (+-suc n₁ n₂)) ((fp , containerⁱ) ∷ Cs)
    where
    containerⁱ : Containerⁱ C α (suc n₁ + n₂)
    Shapeⁱ containerⁱ = length⁺ xs
    Positionⁱ containerⁱ s i = foldr ((λ (m , x) acc → position m i x ∷⁺ acc)) ((λ (m , x) → [ position m i x ])) (lookup (toList xs) s)
      where
      position : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → ModalitySequence (Shape C) → Program C α → Maybe' (Fin n) → Result C α n
      position m i (val x) = apply m i λ { (val o) → res (val (o , x)) ; done → res done ; fail → res fail }
      position m i done = apply m i λ { (val _) → res done ; done → res done ; fail → res fail }
      position m i fail = apply m i λ { (val _) → res fail ; done → res done ; fail → res fail }

  infix 25 _⊨ᵛ_

  _⊨ᵛ_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formulaᵈⁿᶠ-var (Shape C) zero → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  _ ⊨ᵛ trueᵈⁿᶠ = ⊤
  _ ⊨ᵛ falseᵈⁿᶠ = ⊥
  x ⊨ᵛ ⟨ af ⟩ᵈⁿᶠ v with free x
  ... | pure _ = ⊥
  ... | impure (s , c) = s ∈ af × ∃[ p ] c p ⊨ᵛ v
  x ⊨ᵛ [ af ]ᵈⁿᶠ v with free x
  ... | pure _ = ⊤
  ... | impure (s , c) = s ∈ af → ∀ p → c p ⊨ᵛ v
  _⊨ᵛ_ {C = C} {α = α} x (μᵈⁿᶠ d) = Mu (proj₂ (containerize {n₁ = zero} C α leastFP d [])) (val (x , zero))
  _⊨ᵛ_ {C = C} {α = α} x (νᵈⁿᶠ d) = Nu (proj₂ (containerize {n₁ = zero} C α greatestFP d [])) (val (x , zero))

  infix 25 _⊨ᶜ_

  _⊨ᶜ_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formulaᵈⁿᶠ-con (Shape C) zero → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  x ⊨ᶜ con-var v = x ⊨ᵛ v
  x ⊨ᶜ v ∧ᵈⁿᶠ c = x ⊨ᵛ v × x ⊨ᶜ c

  infix 25 _⊨ᵈ_

  _⊨ᵈ_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formulaᵈⁿᶠ-dis (Shape C) zero → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  x ⊨ᵈ dis-con c = x ⊨ᶜ c
  x ⊨ᵈ c ∨ᵈⁿᶠ d = x ⊨ᶜ c ⊎ x ⊨ᵈ d

infix 60 ref_
infix 55 ~_
infix 50 ⟨_⟩_
infix 50 [_]_
infixr 45 _∧_
infixr 40 _∨_
infixr 35 _⇒_
infix 30 μ_．_
infix 30 ν_．_

data Formula (S : Set ℓ) : Set ℓ where
  true false : Formula S
  ~_ : Formula S → Formula S
  _∧_ _∨_ _⇒_ : Formula S → Formula S → Formula S
  ⟨_⟩_ [_]_ : ActionFormula S → Formula S → Formula S
  μ_．_ ν_．_ : String → Formula S → Formula S
  ref_ : String → Formula S

infix 25 _⊨_

_⊨_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formula (Shape C) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
x ⊨ f = x ⊨ⁱ f→fⁱ f []
  where
  f→fⁱ : {S : Set ℓ} → Formula S → (xs : List String) → Formulaⁱ S (length xs)
  f→fⁱ true _ = trueⁱ
  f→fⁱ false _ = falseⁱ
  f→fⁱ (~ f) xs = ~ⁱ f→fⁱ f xs
  f→fⁱ (f₁ ∧ f₂) xs = f→fⁱ f₁ xs ∧ⁱ f→fⁱ f₂ xs
  f→fⁱ (f₁ ∨ f₂) xs = f→fⁱ f₁ xs ∨ⁱ f→fⁱ f₂ xs
  f→fⁱ (f₁ ⇒ f₂) xs = f→fⁱ f₁ xs ⇒ⁱ f→fⁱ f₂ xs
  f→fⁱ (⟨ af ⟩ f) xs = ⟨ af ⟩ⁱ f→fⁱ f xs
  f→fⁱ ([ af ] f) xs = [ af ]ⁱ f→fⁱ f xs
  f→fⁱ (μ x ． f) xs = μⁱ f→fⁱ f (x ∷ xs)
  f→fⁱ (ν x ． f) xs = νⁱ f→fⁱ f (x ∷ xs)
  f→fⁱ (ref x) xs with findIndexᵇ (_==_ x) xs
  ... | just i = refⁱ i
  ... | nothing = falseⁱ
