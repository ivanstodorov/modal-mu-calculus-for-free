{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.FixedPoints.BaseOld where

open import Common.Program using (Program; free; pure; impure)
open import Common.RegularFormulas using (ActionFormula; _∈_)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; length; findIndexᵇ) renaming (lookup to lookup')
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷⁺_; foldr; toList) renaming (length to length⁺)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _<′_; ≤′-refl)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; _==_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Induction.WellFounded using (WellFounded; Acc)
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_; yes; no)

open Bool
open Container
open Fin
open List
open ℕ
open Acc

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

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

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

data Previous (S : Set ℓ) : ℕ → Set ℓ where
  〔_〕 : FixedPoint × Formulaᵈⁿᶠ-dis S (suc zero) → Previous S (suc zero)
  _∷_ : ∀ {n} → FixedPoint × Formulaᵈⁿᶠ-dis S (suc n) → Previous S n → Previous S (suc n)

lookup : {S : Set ℓ} → {n₁ : ℕ} → Previous S n₁ → Fin n₁ → FixedPoint × ∃[ n₂ ] Formulaᵈⁿᶠ-dis S (suc n₂) × Previous S (suc n₂)
lookup prev@(〔 fp , d 〕) zero = fp , zero , d , prev
lookup {n₁ = suc n} prev@((fp , d) ∷ _) zero = fp , n , d , prev
lookup (_ ∷ prev) (suc i) = lookup prev i

data Maybe' (α : Set ℓ) : Set ℓ where
  val_ : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

data Result (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  res_ : Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Result C α
  _×∃_ : ∀ {s} → ActionFormula (Shape C) → (Position C s → Result C α) → Result C α
  _×∀_ : ∀ {s} → ActionFormula (Shape C) → (Position C s → Result C α) → Result C α

unfold : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Result C α → Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
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

unfold⁺ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → (rs : List⁺ (Result C α)) → Acc _<_ rs → Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold⁺ (r ∷ []) _ o x = unfold r o x
unfold⁺ (r₁ ∷ r₂ ∷ rs) (acc h) o x = unfold r₁ o x × unfold⁺ (r₂ ∷ rs) (h ≤′-refl) o x

record Containerⁱ (C : Container ℓ₁ ℓ₂) (α : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shapeⁱ : ℕ
    Positionⁱ : Fin Shapeⁱ → Program C α → List⁺ (Result C α)

open Containerⁱ

data ModalitySequence (S : Set ℓ) : Set ℓ where
  ⟪_⟫_ ⟦_⟧_ : ActionFormula S → ModalitySequence S → ModalitySequence S
  ε : ModalitySequence S

apply : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → ModalitySequence (Shape C) → Program C α → (Maybe' (Program C α) → Result C α) → Result C α
apply (⟪ af ⟫ m) x f with free x
... | pure _ = f fail
... | impure (_ , c) = af ×∃ λ p → apply m (c p) f
apply (⟦ af ⟧ m) x f with free x
... | pure _ = f done
... | impure (_ , c) = af ×∀ λ p → apply m (c p) f
apply ε x f = f (val x)

containerize-var : {S : Set ℓ} → {n₁ : ℕ} → Formulaᵈⁿᶠ-var S (suc n₁) → Previous S (suc n₁) → ModalitySequence S × Maybe' (FixedPoint × ∃[ n₂ ] Formulaᵈⁿᶠ-dis S (suc n₂) × Previous S (suc n₂))
containerize-var trueᵈⁿᶠ _ = ε , done
containerize-var falseᵈⁿᶠ _ = ε , fail
containerize-var (⟨ af ⟩ᵈⁿᶠ v) prev with containerize-var v prev
... | m , x = ⟪ af ⟫ m , x
containerize-var ([ af ]ᵈⁿᶠ v) prev with containerize-var v prev
... | m , x = ⟦ af ⟧ m , x
containerize-var {n₁ = n₁} (μᵈⁿᶠ d) prev = ε , (val (leastFP , suc n₁ , d , (leastFP , d) ∷ prev))
containerize-var {n₁ = n₁} (νᵈⁿᶠ d) prev = ε , (val (greatestFP , suc n₁ , d , (greatestFP , d) ∷ prev))
containerize-var (refᵈⁿᶠ i) prev = ε , val lookup prev i

containerize-con : {S : Set ℓ} → {n₁ : ℕ} → Formulaᵈⁿᶠ-con S (suc n₁) → Previous S (suc n₁) → List⁺ (ModalitySequence S × Maybe' (FixedPoint × ∃[ n₂ ] Formulaᵈⁿᶠ-dis S (suc n₂) × Previous S (suc n₂)))
containerize-con (con-var v) prev = [ containerize-var v prev ]
containerize-con (v ∧ᵈⁿᶠ c) prev = containerize-var v prev ∷⁺ containerize-con c prev

containerize-dis : {S : Set ℓ} → {n₁ : ℕ} → Formulaᵈⁿᶠ-dis S (suc n₁) → Previous S (suc n₁) → List⁺ (List⁺ (ModalitySequence S × Maybe' (FixedPoint × ∃[ n₂ ] Formulaᵈⁿᶠ-dis S (suc n₂) × Previous S (suc n₂))))
containerize-dis (dis-con c) prev = [ containerize-con c prev ]
containerize-dis (c ∨ᵈⁿᶠ d) prev = containerize-con c prev ∷⁺ containerize-dis d prev

containerize : {n : ℕ} → (C : Container ℓ₁ ℓ₂) → (α : Set ℓ₃) → Formulaᵈⁿᶠ-dis (Shape C) (suc n) → Previous (Shape C) (suc n) → Containerⁱ C α
containerize {n = n} C α d prev with containerize-dis d prev
... | xs = containerⁱ
  where
  containerⁱ : Containerⁱ C α
  Shapeⁱ containerⁱ = length⁺ xs
  Positionⁱ containerⁱ s i = foldr (λ (m , x) acc → position m i x ∷⁺ acc) (λ (m , x) → [ position m i x ]) (lookup' (toList xs) s)
    where
    position : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → ModalitySequence (Shape C) → Program C α → Maybe' (FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Result C α
    position m i (val x) = apply m i λ { (val o) → res (val (o , x)) ; done → res done ; fail → res fail }
    position m i done = apply m i λ { (val _) → res done ; done → res done ; fail → res fail }
    position m i fail = apply m i λ { (val _) → res fail ; done → res done ; fail → res fail }

extend : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → (Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
extend {C = C} {α = α} mu _ (val (x , leastFP , _ , d , prev)) = ∃[ s ] ∀ {o} → let rs = Positionⁱ (containerize C α d prev) s x in unfold⁺ rs (<-wf rs) o (mu o)
extend {C = C} {α = α} _ nu (val (x , greatestFP , _ , d , prev)) = ∃[ s ] ∀ {o} → let rs = Positionⁱ (containerize C α d prev) s x in unfold⁺ rs (<-wf rs) o (nu o)
extend _ _ done = ⊤
extend _ _ fail = ⊥

record Mu {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} (_ : Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record Nu {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} (_ : Maybe' (Program C α × FixedPoint × ∃[ n ] Formulaᵈⁿᶠ-dis (Shape C) (suc n) × Previous (Shape C) (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record Mu i where
  inductive
  constructor muᶜ
  field
    mu : extend Mu Nu i

record Nu i where
  coinductive
  constructor nuᶜ
  field
    nu : extend Mu Nu i

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
x ⊨ᵛ μᵈⁿᶠ d = Mu (val (x , leastFP , zero , d , 〔 leastFP , d 〕))
x ⊨ᵛ νᵈⁿᶠ d = Nu (val (x , greatestFP , zero , d , 〔 greatestFP , d 〕))

infix 25 _⊨ᶜ_

_⊨ᶜ_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formulaᵈⁿᶠ-con (Shape C) zero → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
x ⊨ᶜ con-var v = x ⊨ᵛ v
x ⊨ᶜ v ∧ᵈⁿᶠ c = x ⊨ᵛ v × x ⊨ᶜ c

infix 25 _⊨ᵈ_

_⊨ᵈ_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → Program C α → Formulaᵈⁿᶠ-dis (Shape C) zero → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
x ⊨ᵈ dis-con c = x ⊨ᶜ c
x ⊨ᵈ c ∨ᵈⁿᶠ d = x ⊨ᶜ c ⊎ x ⊨ᵈ d

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
