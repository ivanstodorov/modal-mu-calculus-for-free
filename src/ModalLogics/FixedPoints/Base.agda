{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.FixedPoints.Base where

open import Common.Program using (Program)
open import Common.RegularFormulas using (ActionFormula) renaming (_⊩_ to _⊩ᵃᶠ_)
open import Data.Bool using (Bool; not)
open import Data.Container using () renaming (Container to Containerˢᵗᵈ)
open import Data.Container.FreeMonad using (_⋆_)
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
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no)

open Bool
open Containerˢᵗᵈ renaming (Shape to Shapeˢᵗᵈ; Position to Positionˢᵗᵈ)
open _⋆_
open Fin
open List
open ℕ
open Vec
open Acc

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

data Maybe' (α : Set ℓ) : Set ℓ where
  val_ : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

data Result (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  res_ : Maybe' ((C ⋆ α) × Fin n) → Result C α n
  ∃ʳ_ : ∀ {s} → (Positionˢᵗᵈ C s → Result C α n) → Result C α n
  ∀ʳ_ : ∀ {s} → (Positionˢᵗᵈ C s → Result C α n) → Result C α n

unfold : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Result C α n → Maybe' ((C ⋆ α) × Fin n) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold (res v) o x = o ≡ v → x
unfold (∃ʳ c) o x = ∃[ p ] unfold (c p) o x
unfold (∀ʳ c) o x = ∀ p → unfold (c p) o x

_<_ : {α : Set ℓ} → Rel (List⁺ α) 0ℓ
xs < ys = length⁺ xs <′ length⁺ ys

<-wf : {α : Set ℓ} → WellFounded (_<_ {α = α})
<-wf xs = acc<′⇒acc< (<′-wellFounded (length⁺ xs))
  where
    acc<′⇒acc< : {α : Set ℓ} → {xs : List⁺ α} → Acc _<′_ (length⁺ xs) → Acc _<_ xs
    acc<′⇒acc< (acc h) = acc λ hlt → acc<′⇒acc< (h hlt)

unfold⁺ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → (rs : List⁺ (Result C α n)) → Acc _<_ rs → Maybe' ((C ⋆ α) × Fin n) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold⁺ (r ∷ []) _ o x = unfold r o x
unfold⁺ (r₁ ∷ r₂ ∷ rs) (acc h) o x = unfold r₁ o x × unfold⁺ (r₂ ∷ rs) (h ≤′-refl) o x

record Container (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (α : Set ℓ₃) (n : ℕ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shape : ℕ
    Position : Fin Shape → C ⋆ α → List⁺ (Result C α n)

open Container

extend : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Vec (FixedPoint × Container C α (suc n)) (suc n) → (Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Maybe' ((C ⋆ α) × Fin (suc n)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
extend xs w m (val (x , i)) with lookupᵛ xs i
... | leastFP , (S ▷ P) = ∃[ s ] ∀ {o} → let rs = P s x in unfold⁺ rs (<-wf rs) o (w o)
... | greatestFP , (S ▷ P) = ∃[ s ] ∀ {o} → let rs = P s x in unfold⁺ rs (<-wf rs) o (m o)
extend _ _ _ done = ⊤
extend _ _ _ fail = ⊥

record W {C : Containerˢᵗᵈ ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × Container C α (suc n)) (suc n)) (_ : Maybe' ((C ⋆ α) × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record M {C : Containerˢᵗᵈ ℓ₁ ℓ₂} {α : Set ℓ₃} {n : ℕ} (_ : Vec (FixedPoint × Container C α (suc n)) (suc n)) (_ : Maybe' ((C ⋆ α) × Fin (suc n))) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record W xs i where
  inductive
  constructor wᶜ
  field
    In : extend xs (W xs) (M xs) i

record M xs i where
  coinductive
  constructor mᶜ
  field
    Ni : extend xs (W xs) (M xs) i

infix 60 refⁱ_
infix 55 ¬ⁱ_
infix 50 ⟨_⟩ⁱ_
infix 50 [_]ⁱ_
infixr 45 _∧ⁱ_
infixr 40 _∨ⁱ_
infixr 35 _⇒ⁱ_
infix 30 μⁱ_
infix 30 νⁱ_

data Formulaⁱ (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : ℕ → Set ℓ₁ where
  trueⁱ falseⁱ : ∀ {n} → Formulaⁱ C n
  ¬ⁱ_ : ∀ {n} → Formulaⁱ C n → Formulaⁱ C n
  _∧ⁱ_ _∨ⁱ_ _⇒ⁱ_ : ∀ {n} → Formulaⁱ C n → Formulaⁱ C n → Formulaⁱ C n
  ⟨_⟩ⁱ_ [_]ⁱ_ : ∀ {n} → ActionFormula C → Formulaⁱ C n → Formulaⁱ C n
  μⁱ_ νⁱ_ : ∀ {n} → Formulaⁱ C (suc n) → Formulaⁱ C n
  refⁱ_ : ∀ {n} → Fin n → Formulaⁱ C n

infix 25 _⊩ⁱ_

_⊩ⁱ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaⁱ C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
fⁱ ⊩ⁱ x = f'→fᵈⁿᶠ (fⁱ→f' fⁱ) ⊩ᵈ x
  where
  infix 60 ref'〔_〕_
  infix 50 ⟨_⟩'_
  infix 50 [_]'_
  infixr 45 _∧'_
  infixr 40 _∨'_
  infix 30 μ'_
  infix 30 ν'_

  data Formula' (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : ℕ → Set ℓ₁ where
    true' false' : ∀ {n} → Formula' C n
    _∧'_ _∨'_ : ∀ {n} → Formula' C n → Formula' C n → Formula' C n
    ⟨_⟩'_ [_]'_ : ∀ {n} → ActionFormula C → Formula' C n → Formula' C n
    μ'_ ν'_ : ∀ {n} → Formula' C (suc n) → Formula' C n
    ref'〔_〕_ : ∀ {n} → Bool → Fin n → Formula' C n

  flipRef : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Fin n → Formula' C n → Formula' C n
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

  negate : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formula' C n → Formula' C n
  negate true' = false'
  negate false' = true'
  negate (f'₁ ∧' f'₂) = negate f'₁ ∨' negate f'₂
  negate (f'₁ ∨' f'₂) = negate f'₁ ∧' negate f'₂
  negate (⟨ af ⟩' f') = [ af ]' negate f'
  negate ([ af ]' f') = ⟨ af ⟩' negate f'
  negate (μ' f') = ν' flipRef zero f'
  negate (ν' f') = μ' flipRef zero f'
  negate (ref'〔 b 〕 i) = ref'〔 not b 〕 i

  fⁱ→f' : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formulaⁱ C n → Formula' C n
  fⁱ→f' trueⁱ = true'
  fⁱ→f' falseⁱ = false'
  fⁱ→f' (¬ⁱ fⁱ) = negate (fⁱ→f' fⁱ)
  fⁱ→f' (fⁱ₁ ∧ⁱ fⁱ₂) = fⁱ→f' fⁱ₁ ∧' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ∨ⁱ fⁱ₂) = fⁱ→f' fⁱ₁ ∨' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ⇒ⁱ fⁱ₂) = negate (fⁱ→f' fⁱ₁) ∨' fⁱ→f' fⁱ₂
  fⁱ→f' (⟨ af ⟩ⁱ fⁱ) = ⟨ af ⟩' fⁱ→f' fⁱ
  fⁱ→f' ([ af ]ⁱ fⁱ) = [ af ]' fⁱ→f' fⁱ
  fⁱ→f' (μⁱ fⁱ) = μ' fⁱ→f' fⁱ
  fⁱ→f' (νⁱ fⁱ) = ν' fⁱ→f' fⁱ
  fⁱ→f' (refⁱ i) = ref'〔 true 〕 i

  data Formulaᵈⁿᶠ-var (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : ℕ → Set ℓ₁
  data Formulaᵈⁿᶠ-con (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : ℕ → Set ℓ₁
  data Formulaᵈⁿᶠ-dis (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : ℕ → Set ℓ₁

  infix 60 refᵈⁿᶠ_
  infix 55 ⟨_⟩ᵈⁿᶠ_
  infix 55 [_]ᵈⁿᶠ_
  infix 50 μᵈⁿᶠ_
  infix 50 νᵈⁿᶠ_

  data Formulaᵈⁿᶠ-var C where
    trueᵈⁿᶠ falseᵈⁿᶠ : ∀ {n} → Formulaᵈⁿᶠ-var C n
    ⟨_⟩ᵈⁿᶠ_ [_]ᵈⁿᶠ_ : ∀ {n} → ActionFormula C → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-var C n
    μᵈⁿᶠ_ νᵈⁿᶠ_ : ∀ {n} → Formulaᵈⁿᶠ-dis C (suc n) → Formulaᵈⁿᶠ-var C n
    refᵈⁿᶠ_ : ∀ {n} → Fin n → Formulaᵈⁿᶠ-var C n

  infix 45 con-var_
  infixr 40 _∧ᵈⁿᶠ_

  data Formulaᵈⁿᶠ-con C where
    con-var_ : ∀ {n} → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-con C n
    _∧ᵈⁿᶠ_ : ∀ {n} → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n

  infix 35 dis-con_
  infixr 30 _∨ᵈⁿᶠ_

  data Formulaᵈⁿᶠ-dis C where
    dis-con_ : ∀ {n} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-dis C n
    _∨ᵈⁿᶠ_ : ∀ {n} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n

  merge-dis-dis-or : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
  merge-dis-dis-or (dis-con c) d = c ∨ᵈⁿᶠ d
  merge-dis-dis-or (c ∨ᵈⁿᶠ d₁) d₂ = c ∨ᵈⁿᶠ merge-dis-dis-or d₁ d₂

  merge-con-con : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n
  merge-con-con (con-var v) c = v ∧ᵈⁿᶠ c
  merge-con-con (v ∧ᵈⁿᶠ c₁) c₂ = v ∧ᵈⁿᶠ merge-con-con c₁ c₂

  merge-con-dis : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
  merge-con-dis c₁ (dis-con c₂) = dis-con (merge-con-con c₁ c₂)
  merge-con-dis c₁ (c₂ ∨ᵈⁿᶠ d₂) = merge-con-con c₁ c₂ ∨ᵈⁿᶠ merge-con-dis c₁ d₂

  merge-dis-dis-and : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
  merge-dis-dis-and (dis-con c) d = merge-con-dis c d
  merge-dis-dis-and (c ∨ᵈⁿᶠ d₁) d₂ = merge-dis-dis-or (merge-con-dis c d₂) (merge-dis-dis-and d₁ d₂)

  f'→fᵈⁿᶠ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → Formula' C n → Formulaᵈⁿᶠ-dis C n
  f'→fᵈⁿᶠ true' = dis-con (con-var trueᵈⁿᶠ)
  f'→fᵈⁿᶠ false' = dis-con (con-var falseᵈⁿᶠ)
  f'→fᵈⁿᶠ (f'₁ ∧' f'₂) = merge-dis-dis-and (f'→fᵈⁿᶠ f'₁) (f'→fᵈⁿᶠ f'₂)
  f'→fᵈⁿᶠ (f'₁ ∨' f'₂) = merge-dis-dis-or (f'→fᵈⁿᶠ f'₁) (f'→fᵈⁿᶠ f'₂)
  f'→fᵈⁿᶠ (⟨ af ⟩' f') = merge-∃-dis af (f'→fᵈⁿᶠ f')
    where
    merge-∃-var : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-var C n
    merge-∃-var af v = ⟨ af ⟩ᵈⁿᶠ v

    merge-∃-con : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n
    merge-∃-con af (con-var v) = con-var (merge-∃-var af v)
    merge-∃-con af (v ∧ᵈⁿᶠ c) = merge-∃-var af v ∧ᵈⁿᶠ merge-∃-con af c

    merge-∃-dis : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
    merge-∃-dis af (dis-con c) = dis-con (merge-∃-con af c)
    merge-∃-dis af (c ∨ᵈⁿᶠ d) = merge-∃-con af c ∨ᵈⁿᶠ merge-∃-dis af d
  f'→fᵈⁿᶠ ([ af ]' f') = merge-∀-dis af (f'→fᵈⁿᶠ f')
    where
    merge-∀-var : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-var C n
    merge-∀-var af v = [ af ]ᵈⁿᶠ v

    merge-∀-con : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n
    merge-∀-con af (con-var v) = con-var (merge-∀-var af v)
    merge-∀-con af (v ∧ᵈⁿᶠ c) = merge-∀-var af v ∧ᵈⁿᶠ merge-∀-con af c

    merge-∀-dis : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
    merge-∀-dis af (dis-con c) = dis-con (merge-∀-con af c)
    merge-∀-dis af (c ∨ᵈⁿᶠ d) = merge-∀-con af c ∨ᵈⁿᶠ merge-∀-dis af d
  f'→fᵈⁿᶠ (μ' f') = dis-con (con-var (μᵈⁿᶠ f'→fᵈⁿᶠ f'))
  f'→fᵈⁿᶠ (ν' f') = dis-con (con-var (νᵈⁿᶠ f'→fᵈⁿᶠ f'))
  f'→fᵈⁿᶠ (ref'〔 false 〕 _) = dis-con con-var falseᵈⁿᶠ
  f'→fᵈⁿᶠ (ref'〔 true 〕 i) = dis-con (con-var (refᵈⁿᶠ i))

  _↑_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Container C α n → (x : ℕ) → Container C α (n + x)
  Shape ((S ▷ _) ↑ _) = S
  Position ((S ▷ P) ↑ n) s i with P s i
  ... | xs = map⁺ (λ x → x ↑' n) xs
    where
    _↑'_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Result C α n → (x : ℕ) → Result C α (n + x)
    (res (val (fst , snd))) ↑' x = res (val (fst , snd ↑ˡ x))
    (res done) ↑' _ = res done
    (res fail) ↑' _ = res fail
    (∃ʳ c) ↑' n = ∃ʳ λ p → (c p) ↑' n
    (∀ʳ c) ↑' n = ∀ʳ λ p → (c p) ↑' n

  data ModalitySequence (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : Set ℓ₁ where
    ⟪_⟫_ ⟦_⟧_ : ActionFormula C → ModalitySequence C → ModalitySequence C
    ε : ModalitySequence C

  apply : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → {n : ℕ} → ModalitySequence C → C ⋆ α → (Maybe' (C ⋆ α) → Result C α n) → Result C α n
  apply (⟪ _ ⟫ _) (pure _) f = f fail
  apply (⟪ af ⟫ m) (impure (s , c)) f with af ⊩ᵃᶠ s
  ... | false = f fail
  ... | true = ∃ʳ λ p → apply m (c p) f
  apply (⟦ _ ⟧ _) (pure _) f = f done
  apply (⟦ af ⟧ m) (impure (s , c)) f with af ⊩ᵃᶠ s
  ... | false = f done
  ... | true = ∀ʳ λ p → apply m (c p) f
  apply ε x f = f (val x)

  containerize-var : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {n : ℕ} → Formulaᵈⁿᶠ-var C (suc n) → (n₁ : ℕ) → Vec (Fin (suc n₁)) (suc n) → (α : Set ℓ₃) → ModalitySequence C × Maybe' (∃[ n₂ ] (Fin (suc n₁ + n₂)) × Vec (FixedPoint × Container C α (suc n₁ + n₂)) n₂)
  containerize-con : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {n : ℕ} → Formulaᵈⁿᶠ-con C (suc n) → (n₁ : ℕ) → Vec (Fin (suc n₁)) (suc n) → (α : Set ℓ₃) → ∃[ n₂ ] List⁺ (ModalitySequence C × Maybe' (Fin (suc n₁ + n₂))) × Vec (FixedPoint × Container C α (suc n₁ + n₂)) n₂
  containerize-dis : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {n : ℕ} → Formulaᵈⁿᶠ-dis C (suc n) → (n₁ : ℕ) → Vec (Fin (suc n₁)) (suc n) → (α : Set ℓ₃) → ∃[ n₂ ] List⁺ (List⁺ (ModalitySequence C × Maybe' (Fin (suc n₁ + n₂)))) × Vec (FixedPoint × Container C α (suc n₁ + n₂)) n₂
  containerize : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {n : ℕ} → FixedPoint → Formulaᵈⁿᶠ-dis C (suc n) → (n₁ : ℕ) → Vec (Fin n₁) n → (α : Set ℓ₃) → ∃[ n₂ ] Vec (FixedPoint × Container C α (n₁ + suc n₂)) (suc n₂)

  containerize-var trueᵈⁿᶠ _ _ _ = ε , done
  containerize-var falseᵈⁿᶠ _ _ _ = ε , fail
  containerize-var (⟨ af ⟩ᵈⁿᶠ v) n₁ prev α with containerize-var v n₁ prev α
  ... | m , x = ⟪ af ⟫ m , x
  containerize-var ([ af ]ᵈⁿᶠ v) n₁ prev α with containerize-var v n₁ prev α
  ... | m , x = ⟦ af ⟧ m , x
  containerize-var (μᵈⁿᶠ d) n₁ prev α with containerize leastFP d (suc n₁) prev α
  ... | n₂ , Cs = ε , val (suc n₂ , subst Fin (sym (+-suc (suc n₁) n₂)) (fromℕ< (m≤n⇒m≤n+o n₂ (n<1+n (suc n₁)))) , Cs)
  containerize-var (νᵈⁿᶠ d) n₁ prev α with containerize greatestFP d (suc n₁) prev α
  ... | n₂ , Cs = ε , val (suc n₂ , subst Fin (sym (+-suc (suc n₁) n₂)) (fromℕ< (m≤n⇒m≤n+o n₂ (n<1+n (suc n₁)))) , Cs)
  containerize-var (refᵈⁿᶠ i) n₁ prev α = ε , val (zero , subst Fin (sym (+-identityʳ (suc n₁))) (lookupᵛ prev i) , [])

  containerize-con (con-var v) n₁ prev α with containerize-var v n₁ prev α
  ... | m , val (n₂ , i , Cs) = n₂ , [ m , val i ] , Cs
  ... | m , done = zero , [ m , done ] , []
  ... | m , fail = zero , [ m , fail ] , []
  containerize-con (v ∧ᵈⁿᶠ c) n₁ prev α with containerize-var v n₁ prev α
  containerize-con {C = C} (v ∧ᵈⁿᶠ c) n₁ prev α | m , val (n₂ , i , Cs₁) with containerize-con c (n₁ + n₂) (mapᵛ (λ x → x ↑ˡ n₂) prev) α
  ... | n₃ , xs , Cs₂ = n₂ + n₃ , subst (λ n → List⁺ (ModalitySequence C × Maybe' (Fin n)) × Vec (FixedPoint × Container C α n) (n₂ + n₃)) (+-assoc (suc n₁) n₂ n₃) ((m , val (fromℕ< (m≤n⇒m≤n+o n₃ (n<1+n (n₁ + n₂))))) ∷⁺ xs , mapᵛ (λ (fp , C) → fp , (C ↑ n₃)) Cs₁ ++ Cs₂)
  containerize-con (v ∧ᵈⁿᶠ c) n₁ prev α | m , done with containerize-con c n₁ prev α
  ... | n₂ , xs , Cs = n₂ , (m , done) ∷⁺ xs , Cs
  containerize-con (v ∧ᵈⁿᶠ c) n₁ prev α | m , fail with containerize-con c n₁ prev α
  ... | n₂ , xs , Cs = n₂ , (m , fail) ∷⁺ xs , Cs

  containerize-dis (dis-con c) n₁ prev α with containerize-con c n₁ prev α
  ... | n₂ , x , Cs = n₂ , [ x ] , Cs
  containerize-dis {C = C} (c ∨ᵈⁿᶠ d) n₁ prev α with containerize-con c n₁ prev α
  ... | n₂ , x , Cs₁ with containerize-dis d (n₁ + n₂) (mapᵛ (λ x → x ↑ˡ n₂) prev) α
  ...   | n₃ , xs , Cs₂ = n₂ + n₃ , subst (λ n → List⁺ (List⁺ (ModalitySequence C × Maybe' (Fin n))) × Vec (FixedPoint × Container C α n) (n₂ + n₃)) (+-assoc (suc n₁) n₂ n₃) (map⁺ (λ { (m , val x) → m , val (x ↑ˡ n₃) ; (m , done) → m , done ; (m , fail) → m , fail }) x ∷⁺ xs , mapᵛ (λ (fp , C) → fp , (C ↑ n₃)) Cs₁ ++ Cs₂)

  containerize {C = C} fp d n₁ prev α with containerize-dis d n₁ (fromℕ< (n<1+n n₁) ∷ mapᵛ inject₁ prev) α
  ... | n₂ , xs , Cs = n₂ , subst (λ n → Vec (FixedPoint × Container C α n) (suc n₂)) (sym (+-suc n₁ n₂)) ((fp , container) ∷ Cs)
    where
    container : Container C α (suc n₁ + n₂)
    Shape container = length⁺ xs
    Position container s i = foldr ((λ (m , x) acc → position m i x ∷⁺ acc)) ((λ (m , x) → [ position m i x ])) (lookup (toList xs) s)
      where
      position : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → {n : ℕ} → ModalitySequence C → C ⋆ α → Maybe' (Fin n) → Result C α n
      position m i (val x) = apply m i λ { (val o) → res (val (o , x)) ; done → res done ; fail → res fail }
      position m i done = apply m i λ { (val _) → res done ; done → res done ; fail → res fail }
      position m i fail = apply m i λ { (val _) → res fail ; done → res done ; fail → res fail }

  infix 25 _⊩ᵛ_

  _⊩ᵛ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-var C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  trueᵈⁿᶠ ⊩ᵛ _ = ⊤
  falseᵈⁿᶠ ⊩ᵛ _ = ⊥
  ⟨ _ ⟩ᵈⁿᶠ _ ⊩ᵛ pure _ = ⊥
  ⟨ af ⟩ᵈⁿᶠ v ⊩ᵛ impure (s , c) with af ⊩ᵃᶠ s
  ... | false = ⊥
  ... | true = ∃[ p ] v ⊩ᵛ c p
  [ _ ]ᵈⁿᶠ _ ⊩ᵛ pure _ = ⊤
  [ af ]ᵈⁿᶠ v ⊩ᵛ impure (s , c) with af ⊩ᵃᶠ s
  ... | false = ⊤
  ... | true = ∀ p → v ⊩ᵛ c p
  _⊩ᵛ_ {α = α} (μᵈⁿᶠ d) x = W (proj₂ (containerize leastFP d zero [] α)) (val (x , zero))
  _⊩ᵛ_ {α = α} (νᵈⁿᶠ d) x = M (proj₂ (containerize greatestFP d zero [] α)) (val (x , zero))

  infix 25 _⊩ᶜ_

  _⊩ᶜ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-con C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  con-var v ⊩ᶜ x = v ⊩ᵛ x
  v ∧ᵈⁿᶠ c ⊩ᶜ x = (v ⊩ᵛ x) × (c ⊩ᶜ x)

  infix 25 _⊩ᵈ_

  _⊩ᵈ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-dis C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  dis-con c ⊩ᵈ x = c ⊩ᶜ x
  c ∨ᵈⁿᶠ d ⊩ᵈ x = (c ⊩ᶜ x) ⊎ (d ⊩ᵈ x)

infix 60 ref_
infix 55 ¬_
infix 50 ⟨_⟩_
infix 50 [_]_
infixr 45 _∧_
infixr 40 _∨_
infixr 35 _⇒_
infix 30 μ_．_
infix 30 ν_．_

data Formula (C : Containerˢᵗᵈ ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ¬_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : ActionFormula C → Formula C → Formula C
  μ_．_ ν_．_ : String → Formula C → Formula C
  ref_ : String → Formula C

infix 25 _⊩_

_⊩_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ⊩ x = f→fⁱ f [] ⊩ⁱ x
  where
  f→fⁱ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → Formula C → (xs : List String) → Formulaⁱ C (length xs)
  f→fⁱ true _ = trueⁱ
  f→fⁱ false _ = falseⁱ
  f→fⁱ (¬ f) xs = ¬ⁱ f→fⁱ f xs
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

infix 25 _⊩_〔_〕

_⊩_〔_〕 : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C → Program C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
f ⊩ x 〔 i 〕 = f ⊩ x i
