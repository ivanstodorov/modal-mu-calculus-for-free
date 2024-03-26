{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.Final.Base where

open import Data.Container using () renaming (Container to Containerˢᵗᵈ)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List) renaming (lookup to lookup')
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷⁺_; foldr; toList) renaming (length to length⁺)
open import Data.Nat using (ℕ; _<′_; ≤′-refl)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec) renaming (length to lengthᵛ; [_] to [_]ᵛ; lookup to lookupᵛ)
open import Function using (case_of_)
open import Induction.WellFounded using (WellFounded; Acc)
open import Level using (Level; 0ℓ; _⊔_; Lift) renaming (suc to sucˡ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬'_)

open Containerˢᵗᵈ renaming (Shape to Shapeˢᵗᵈ; Position to Positionˢᵗᵈ)
open _⋆_
open Fin
open List
open ℕ
open _⊎_
open Vec
open Acc
open IsDecEquivalence ⦃...⦄

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

data Inhabited (α : Set ℓ) : Set ℓ where
  default_ : α → Inhabited α

data ActionFormula (_ : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁)

infix 90 val_
infix 90 act_
infix 85 ¬_
infixr 80 _∩_
infixr 80 _∪_
infix 75 ∀〔_〕_
infix 75 ∃〔_〕_

data ActionFormula C ℓ where
  val_ : Set ℓ → ActionFormula C ℓ
  true false : ActionFormula C ℓ
  act_ : Shapeˢᵗᵈ C → ActionFormula C ℓ
  ¬_ : ActionFormula C ℓ → ActionFormula C ℓ
  _∩_ _∪_ : ActionFormula C ℓ → ActionFormula C ℓ → ActionFormula C ℓ
  ∀〔_〕_ ∃〔_〕_ : ∀ {α : Set ℓ} → Inhabited α → (α → ActionFormula C ℓ) → ActionFormula C ℓ

infix 25 _⊩ᵃᶠ_

_⊩ᵃᶠ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence (_≡_ {A = Shapeˢᵗᵈ C}) ⦄ → ActionFormula C ℓ → Shapeˢᵗᵈ C → Set ℓ
val x ⊩ᵃᶠ _ = x
true ⊩ᵃᶠ _ = ⊤
false ⊩ᵃᶠ _ = ⊥
act x ⊩ᵃᶠ s with x ≟ s
... | no _ = ⊥
... | yes _ = ⊤
¬ af ⊩ᵃᶠ s = ¬' (af ⊩ᵃᶠ s)
af₁ ∩ af₂ ⊩ᵃᶠ s = (af₁ ⊩ᵃᶠ s) × (af₂ ⊩ᵃᶠ s)
af₁ ∪ af₂ ⊩ᵃᶠ s = (af₁ ⊩ᵃᶠ s) ⊎ (af₂ ⊩ᵃᶠ s)
∀〔 _ 〕 af ⊩ᵃᶠ s = ∀ a → (af a) ⊩ᵃᶠ s
∃〔 _ 〕 af ⊩ᵃᶠ s = ∃[ a ] (af a) ⊩ᵃᶠ s

infix 70 actF_
infix 65 _*
infix 65 _⁺
infixr 60 _·_
infixr 60 _+_

data RegularFormula (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁) where
  ε : RegularFormula C ℓ
  actF_ : ActionFormula C ℓ → RegularFormula C ℓ
  _·_ _+_ : RegularFormula C ℓ → RegularFormula C ℓ → RegularFormula C ℓ
  _* _⁺ : RegularFormula C ℓ → RegularFormula C ℓ

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {α αs} → α → Arguments ℓ αs → Arguments ℓ (α ∷ αs)

data Formulaᵈⁿᶠ-var {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)
data Formulaᵈⁿᶠ-con {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)
data Formulaᵈⁿᶠ-dis {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)

data Quantifiedᵈⁿᶠ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ ⊎ Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
  formulaᵈⁿᶠ_ : Formulaᵈⁿᶠ-dis C ℓ xs → Quantifiedᵈⁿᶠ C ℓ xs []
  ∀ᵈⁿᶠ〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantifiedᵈⁿᶠ C ℓ xs αs) → Quantifiedᵈⁿᶠ C ℓ xs (inj₁ α ∷ αs)
  ∃ᵈⁿᶠ〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantifiedᵈⁿᶠ C ℓ xs αs) → Quantifiedᵈⁿᶠ C ℓ xs (inj₂ α ∷ αs)

data Parameterizedᵈⁿᶠ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
  quantifiedᵈⁿᶠ_ : ∀ {αs} → Quantifiedᵈⁿᶠ C ℓ xs αs → Parameterizedᵈⁿᶠ C ℓ xs []
  _↦ᵈⁿᶠ_ : ∀ {αs : List (Set ℓ)} → (α : Set ℓ) → (α → Parameterizedᵈⁿᶠ C ℓ xs αs) → Parameterizedᵈⁿᶠ C ℓ xs (α ∷ αs)

infix 55 valᵈⁿᶠ_
infix 55 refᵈⁿᶠ_．_
infix 50 ⟨_⟩ᵈⁿᶠ_
infix 50 [_]ᵈⁿᶠ_
infix 50 μᵈⁿᶠ_．_
infix 50 νᵈⁿᶠ_．_

data Formulaᵈⁿᶠ-var C ℓ where
  trueᵈⁿᶠ falseᵈⁿᶠ : ∀ {xs} → Formulaᵈⁿᶠ-var C ℓ xs
  valᵈⁿᶠ_ : ∀ {xs} → Set ℓ → Formulaᵈⁿᶠ-var C ℓ xs
  ⟨_⟩ᵈⁿᶠ_ [_]ᵈⁿᶠ_ : ∀ {xs} → ActionFormula C ℓ → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-var C ℓ xs
  μᵈⁿᶠ_．_ νᵈⁿᶠ_．_ : ∀ {αs xs} → Parameterizedᵈⁿᶠ C ℓ (αs ∷ xs) αs → Arguments ℓ αs → Formulaᵈⁿᶠ-var C ℓ xs
  refᵈⁿᶠ_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ (lookupᵛ xs i) → Formulaᵈⁿᶠ-var C ℓ xs

infix 45 con-var_
infixr 40 _∧ᵈⁿᶠ_

data Formulaᵈⁿᶠ-con C ℓ where
  con-var_ : ∀ {xs} → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs
  _∧ᵈⁿᶠ_ : ∀ {xs} → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs

infix 35 dis-con_
infixr 30 _∨ᵈⁿᶠ_

data Formulaᵈⁿᶠ-dis C ℓ where
  dis-con_ : ∀ {xs} → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs
  _∨ᵈⁿᶠ_ : ∀ {xs} → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

data Previous (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : {n : ℕ} → Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂) where
  〔_〕 : ∀ {αs : List (Set ℓ)} → FixedPoint × Parameterizedᵈⁿᶠ C ℓ [ αs ]ᵛ αs → Previous C ℓ [ αs ]ᵛ
  _∷_ : ∀ {αs : List (Set ℓ)} {n : ℕ} {xs : Vec (List (Set ℓ)) n} → FixedPoint × Parameterizedᵈⁿᶠ C ℓ (αs ∷ xs) αs → Previous C ℓ xs → Previous C ℓ (αs ∷ xs)

lookup : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {n₁ : ℕ} → {xs₁ : Vec (List (Set ℓ)) n₁} → Previous C ℓ xs₁ → (i : Fin n₁) → FixedPoint × ∃[ n₂ ] ∃[ xs₂ ] Parameterizedᵈⁿᶠ {n = suc n₂} C ℓ ((lookupᵛ xs₁ i) ∷ xs₂) (lookupᵛ xs₁ i) × Previous C ℓ ((lookupᵛ xs₁ i) ∷ xs₂)
lookup {xs₁ = αs ∷ []} prev@(〔 fp , p 〕) zero = fp , zero , [] , p , prev
lookup {n₁ = suc n} {xs₁ = αs ∷ xs} prev@((fp , p) ∷ _) zero = fp , n , xs , p , prev
lookup (_ ∷ prev) (suc i) = lookup prev i

data Maybe' (α : Set ℓ) : Set ℓ where
  val_ : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

data Result (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (X : Set ℓ₃) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  res_ : Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Result C X ℓ
  _×∃_ : ∀ {s} → ActionFormula C ℓ → (Positionˢᵗᵈ C s → Result C X ℓ) → Result C X ℓ
  _×∀_ : ∀ {s} → ActionFormula C ℓ → (Positionˢᵗᵈ C s → Result C X ℓ) → Result C X ℓ

unfold-r : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → Result C X ℓ → Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold-r (res v) o x = o ≡ v → x
unfold-r (_×∃_ {s = s} af c) o x = af ⊩ᵃᶠ s × ∃[ p ] unfold-r (c p) o x
unfold-r (_×∀_ {s = s} af c) o x = af ⊩ᵃᶠ s × ∀ p → unfold-r (c p) o x

_<_ : {X : Set ℓ} → Rel (List⁺ X) 0ℓ
xs < ys = length⁺ xs <′ length⁺ ys

<-wf : {X : Set ℓ} → WellFounded (_<_ {X = X})
<-wf xs = acc<′⇒acc< (<′-wellFounded (length⁺ xs))
  where
    acc<′⇒acc< : {X : Set ℓ} → {xs : List⁺ X} → Acc _<′_ (length⁺ xs) → Acc _<_ xs
    acc<′⇒acc< (acc h) = acc λ hlt → acc<′⇒acc< (h hlt)

unfold-rs : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → (rs : List⁺ (Result C X ℓ)) → Acc _<_ rs → Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold-rs (r ∷ []) _ o x = unfold-r r o x
unfold-rs (r₁ ∷ r₂ ∷ rs) (acc h) o x = unfold-r r₁ o x × unfold-rs (r₂ ∷ rs) (h ≤′-refl) o x

record Container {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (X : Set ℓ₃) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shape : ℕ
    Position : Fin Shape → C ⋆ X → List⁺ (Result C X ℓ)

open Container

data ModalitySequence (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁) where
  ⟪_⟫_ ⟦_⟧_ : ActionFormula C ℓ → ModalitySequence C ℓ → ModalitySequence C ℓ
  ε : ModalitySequence C ℓ

unfold : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → ModalitySequence C ℓ → C ⋆ X → (Maybe' (C ⋆ X) → Result C X ℓ) → Result C X ℓ
unfold (⟪ _ ⟫ _) (pure _) f = f fail
unfold (⟪ af ⟫ m) (impure (_ , c)) f = af ×∃ λ p → unfold m (c p) f
unfold (⟦ _ ⟧ _) (pure _) f = f done
unfold (⟦ af ⟧ m) (impure (_ , c)) f = af ×∀ λ p → unfold m (c p) f
unfold ε x f = f (val x)

containerize-var : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {n : ℕ} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-var C ℓ (x ∷ xs) → Previous C ℓ (x ∷ xs) → ModalitySequence C ℓ × Maybe' (Set ℓ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs))
containerize-var trueᵈⁿᶠ _ = ε , done
containerize-var falseᵈⁿᶠ _ = ε , fail
containerize-var (valᵈⁿᶠ x) _ = ε , val inj₁ x
containerize-var (⟨ af ⟩ᵈⁿᶠ v) prev with containerize-var v prev
... | m , x = ⟪ af ⟫ m , x
containerize-var ([ af ]ᵈⁿᶠ v) prev with containerize-var v prev
... | m , x = ⟦ af ⟧ m , x
containerize-var {n = n} {x = x} {xs = xs} (μᵈⁿᶠ_．_ {αs = αs} p args) prev = ε , val inj₂ (leastFP , suc n , x ∷ xs , αs , p , (leastFP , p) ∷ prev , args)
containerize-var {n = n} {x = x} {xs = xs} (νᵈⁿᶠ_．_ {αs = αs} p args) prev = ε , val inj₂ (greatestFP , suc n , x ∷ xs , αs , p , (greatestFP , p) ∷ prev , args)
containerize-var {x = x} {xs = xs} (refᵈⁿᶠ i ． args) prev with lookup prev i
... | fp , n , xs₁ , p , prev = ε , val inj₂ (fp , n , xs₁ , lookupᵛ (x ∷ xs) i , p , prev , args)

containerize-con : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {n : ℕ} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-con C ℓ (x ∷ xs) → Previous C ℓ (x ∷ xs) → List⁺ (ModalitySequence C ℓ × Maybe' (Set ℓ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)))
containerize-con (con-var v) prev = [ containerize-var v prev ]
containerize-con (v ∧ᵈⁿᶠ c) prev = containerize-var v prev ∷⁺ containerize-con c prev

containerize-dis : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {n : ℕ} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-dis C ℓ (x ∷ xs) → Previous C ℓ (x ∷ xs) → List⁺ (List⁺ (ModalitySequence C ℓ × Maybe' (Set ℓ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs))))
containerize-dis (dis-con c) prev = [ containerize-con c prev ]
containerize-dis (c ∨ᵈⁿᶠ d) prev = containerize-con c prev ∷⁺ containerize-dis d prev

containerize : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {n : ℕ} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-dis C ℓ (x ∷ xs) → Previous C ℓ (x ∷ xs) → (X : Set ℓ₃) → Container C X ℓ (x ∷ xs)
containerize {C = C} {ℓ = ℓ} {n = n} {x = X} {xs = Xs} d prev α with containerize-dis d prev
... | xs = result
  where
  result : Container C α ℓ (X ∷ Xs)
  Shape result = length⁺ xs
  Position result s i = foldr (λ (m , x) acc → position m i x ∷⁺ acc) (λ (m , x) → [ position m i x ]) (lookup' (toList xs) s)
    where
    position : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → ModalitySequence C ℓ → C ⋆ X → Maybe' (Set ℓ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Result C X ℓ
    position m i (val inj₁ x) = unfold m i λ { (val _) → res (val inj₁ x) ; done → res done ; fail → res fail }
    position m i (val inj₂ x) = unfold m i λ { (val o) → res (val inj₂ (o , x)) ; done → res done ; fail → res fail }
    position m i done = unfold m i λ { (val _) → res done ; done → res done ; fail → res fail }
    position m i fail = unfold m i λ { (val _) → res fail ; done → res done ; fail → res fail }

extend : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → (Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
extend {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} {ℓ = ℓ} (val inj₁ x) _ _ = Lift ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) x
extend (val inj₂ (x , fp , _ , _ , _ , p , prev , args)) w m = quantify (proj₂ (apply p args)) prev x (case fp of λ { leastFP → w ; greatestFP → m })
  where
  apply : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {n : ℕ} → {xs : Vec (List (Set ℓ)) n} → {αs₁ : List (Set ℓ)} → Parameterizedᵈⁿᶠ C ℓ xs αs₁ → Arguments ℓ αs₁ → ∃[ αs₂ ] Quantifiedᵈⁿᶠ C ℓ xs αs₂
  apply (quantifiedᵈⁿᶠ_ {αs = αs} q) [] = αs , q
  apply (_ ↦ᵈⁿᶠ p) (a ∷ args) = apply (p a) args

  quantify : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → {n : ℕ} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ ⊎ Set ℓ)} → Quantifiedᵈⁿᶠ C ℓ (x ∷ xs) αs → Previous C ℓ (x ∷ xs) → C ⋆ X → (Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  quantify {X = X} (formulaᵈⁿᶠ d) prev x f = ∃[ s ] ∀ {o} → let rs = Position (containerize d prev X) s x in unfold-rs rs (<-wf rs) o (f o)
  quantify (∀ᵈⁿᶠ〔 _ 〕 q) prev x f = ∀ a → quantify (q a) prev x f
  quantify (∃ᵈⁿᶠ〔 _ 〕 q) prev x f = ∃[ a ] quantify (q a) prev x f
extend done _ _ = ⊤
extend fail _ _ = ⊥

record WI {C : Containerˢᵗᵈ ℓ₁ ℓ₂} ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ {X : Set ℓ₃} {ℓ : Level} (_ : Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs))) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record MI {C : Containerˢᵗᵈ ℓ₁ ℓ₂} ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ {X : Set ℓ₃} {ℓ : Level} (_ : Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs))) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record WI i where
  inductive
  constructor wi
  field
    In : extend i WI MI

record MI i where
  coinductive
  constructor mi
  field
    Ni : extend i WI MI

infix 25 _⊩ᵛ_

_⊩ᵛ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → Formulaᵈⁿᶠ-var C ℓ [] → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
trueᵈⁿᶠ ⊩ᵛ _ = ⊤
falseᵈⁿᶠ ⊩ᵛ _ = ⊥
_⊩ᵛ_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} {ℓ = ℓ} (valᵈⁿᶠ x) _ = Lift ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) x
⟨ _ ⟩ᵈⁿᶠ _ ⊩ᵛ pure _ = ⊥
⟨ af ⟩ᵈⁿᶠ v ⊩ᵛ impure (s , c) = af ⊩ᵃᶠ s × ∃[ p ] v ⊩ᵛ c p
[ _ ]ᵈⁿᶠ _ ⊩ᵛ pure _ = ⊤
[ af ]ᵈⁿᶠ v ⊩ᵛ impure (s , c) = af ⊩ᵃᶠ s × ∀ p → v ⊩ᵛ c p
μᵈⁿᶠ_．_ {αs = αs} p args ⊩ᵛ x = WI (val inj₂ (x , leastFP , zero , [] , αs , p , 〔 leastFP , p 〕 , args))
νᵈⁿᶠ_．_ {αs = αs} p args ⊩ᵛ x = MI (val inj₂ (x , greatestFP , zero , [] , αs , p , 〔 greatestFP , p 〕 , args))

infix 25 _⊩ᶜ_

_⊩ᶜ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → Formulaᵈⁿᶠ-con C ℓ [] → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
con-var v ⊩ᶜ x = v ⊩ᵛ x
v ∧ᵈⁿᶠ c ⊩ᶜ x = (v ⊩ᵛ x) × (c ⊩ᶜ x)

infix 25 _⊩ᵈ_

_⊩ᵈ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → Formulaᵈⁿᶠ-dis C ℓ [] → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
dis-con c ⊩ᵈ x = c ⊩ᶜ x
c ∨ᵈⁿᶠ d ⊩ᵈ x = (c ⊩ᶜ x) ⊎ (d ⊩ᵈ x)
