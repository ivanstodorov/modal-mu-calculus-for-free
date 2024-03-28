{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.DataParameters.Base where

open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Bool using (Bool; not; T)
open import Data.Container using () renaming (Container to Containerˢᵗᵈ)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; toℕ; inject₁; cast) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List) renaming (lookup to lookup')
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷⁺_; foldr; toList) renaming (length to length⁺)
open import Data.Nat using (ℕ; _<ᵇ_; _<′_; ≤′-refl; z≤n; s≤s; _≥_) renaming (_+_ to _＋_; _<_ to _<ⁿ_)
open import Data.Nat.Properties using (+-suc; <ᵇ⇒<; <⇒<ᵇ; ≮⇒≥)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; _++_) renaming (length to lengthᵛ; [_] to [_]ᵛ; lookup to lookupᵛ)
open import Function using (case_of_)
open import Induction.WellFounded using (WellFounded; Acc)
open import Level using (Level; 0ℓ; _⊔_; Lift) renaming (suc to sucˡ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; subst; sym) renaming ([_] to [_]⁼)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no) renaming (¬_ to ¬ˢᵗᵈ_)

open Bool
open Containerˢᵗᵈ renaming (Shape to Shapeˢᵗᵈ; Position to Positionˢᵗᵈ)
open _⋆_
open Fin
open List
open ℕ
open _⊎_
open Vec
open Acc
open _≡_
open IsDecEquivalence ⦃...⦄ hiding (refl; sym)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Inhabited (α : Set ℓ) : Set ℓ where
  default_ : α → Inhabited α

module ActionFormulas where

  infix 125 val_
  infix 125 act_
  infix 120 ¬_
  infixr 115 _∩_
  infixr 110 _∪_
  infix 105 ∀〔_〕_
  infix 105 ∃〔_〕_

  data ActionFormula (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁) where
    true false : ActionFormula C ℓ
    val_ : Set ℓ → ActionFormula C ℓ
    act_ : Shapeˢᵗᵈ C → ActionFormula C ℓ
    ¬_ : ActionFormula C ℓ → ActionFormula C ℓ
    _∩_ _∪_ : ActionFormula C ℓ → ActionFormula C ℓ → ActionFormula C ℓ
    ∀〔_〕_ ∃〔_〕_ : ∀ {α : Set ℓ} → Inhabited α → (α → ActionFormula C ℓ) → ActionFormula C ℓ

  infix 25 _⊩_

  _⊩_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence (_≡_ {A = Shapeˢᵗᵈ C}) ⦄ → ActionFormula C ℓ → Shapeˢᵗᵈ C → Set ℓ
  true ⊩ _ = ⊤
  false ⊩ _ = ⊥
  val x ⊩ _ = x
  act x ⊩ s with x ≟ s
  ... | no _ = ⊥
  ... | yes _ = ⊤
  ¬ af ⊩ s = ¬ˢᵗᵈ (af ⊩ s)
  af₁ ∩ af₂ ⊩ s = (af₁ ⊩ s) × (af₂ ⊩ s)
  af₁ ∪ af₂ ⊩ s = (af₁ ⊩ s) ⊎ (af₂ ⊩ s)
  ∀〔 _ 〕 af ⊩ s = ∀ a → (af a) ⊩ s
  ∃〔 _ 〕 af ⊩ s = ∃[ a ] (af a) ⊩ s

open ActionFormulas using (ActionFormula) renaming (_⊩_ to _⊩ᵃᶠ_)

module RegularFormulas where

  infix 100 actF_
  infix 95 _*
  infix 95 _⁺
  infixr 90 _·_
  infixr 85 _+_

  data RegularFormula (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁) where
    ε : RegularFormula C ℓ
    actF_ : ActionFormula C ℓ → RegularFormula C ℓ
    _·_ _+_ : RegularFormula C ℓ → RegularFormula C ℓ → RegularFormula C ℓ
    _* _⁺ : RegularFormula C ℓ → RegularFormula C ℓ

open RegularFormulas using (RegularFormula)

open RegularFormula

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {α αs} → α → Arguments ℓ αs → Arguments ℓ (α ∷ αs)

data Formulaᵈⁿᶠ-var {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)
data Formulaᵈⁿᶠ-con {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)
data Formulaᵈⁿᶠ-dis {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)

infix 45 formulaᵈⁿᶠ_
infix 40 ∀ᵈⁿᶠ〔_〕_
infix 40 ∃ᵈⁿᶠ〔_〕_

data Quantifiedᵈⁿᶠ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ ⊎ Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
  formulaᵈⁿᶠ_ : Formulaᵈⁿᶠ-dis C ℓ xs → Quantifiedᵈⁿᶠ C ℓ xs []
  ∀ᵈⁿᶠ〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantifiedᵈⁿᶠ C ℓ xs αs) → Quantifiedᵈⁿᶠ C ℓ xs (inj₁ α ∷ αs)
  ∃ᵈⁿᶠ〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantifiedᵈⁿᶠ C ℓ xs αs) → Quantifiedᵈⁿᶠ C ℓ xs (inj₂ α ∷ αs)

infix 35 quantifiedᵈⁿᶠ_
infix 30 _↦ᵈⁿᶠ_

data Parameterizedᵈⁿᶠ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
  quantifiedᵈⁿᶠ_ : ∀ {αs} → Quantifiedᵈⁿᶠ C ℓ xs αs → Parameterizedᵈⁿᶠ C ℓ xs []
  _↦ᵈⁿᶠ_ : ∀ {αs : List (Set ℓ)} → (α : Set ℓ) → (α → Parameterizedᵈⁿᶠ C ℓ xs αs) → Parameterizedᵈⁿᶠ C ℓ xs (α ∷ αs)

infix 80 valᵈⁿᶠ_
infix 80 refᵈⁿᶠ_．_
infix 75 ⟨_⟩ᵈⁿᶠ_
infix 75 [_]ᵈⁿᶠ_
infix 70 μᵈⁿᶠ_．_
infix 70 νᵈⁿᶠ_．_

data Formulaᵈⁿᶠ-var C ℓ where
  trueᵈⁿᶠ falseᵈⁿᶠ : ∀ {xs} → Formulaᵈⁿᶠ-var C ℓ xs
  valᵈⁿᶠ_ : ∀ {xs} → Set ℓ → Formulaᵈⁿᶠ-var C ℓ xs
  ⟨_⟩ᵈⁿᶠ_ [_]ᵈⁿᶠ_ : ∀ {xs} → ActionFormula C ℓ → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-var C ℓ xs
  μᵈⁿᶠ_．_ νᵈⁿᶠ_．_ : ∀ {αs xs} → Parameterizedᵈⁿᶠ C ℓ (αs ∷ xs) αs → Arguments ℓ αs → Formulaᵈⁿᶠ-var C ℓ xs
  refᵈⁿᶠ_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ (lookupᵛ xs i) → Formulaᵈⁿᶠ-var C ℓ xs

infix 65 con-var_
infixr 60 _∧ᵈⁿᶠ_

data Formulaᵈⁿᶠ-con C ℓ where
  con-var_ : ∀ {xs} → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs
  _∧ᵈⁿᶠ_ : ∀ {xs} → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs

infix 55 dis-con_
infixr 50 _∨ᵈⁿᶠ_

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

unfold : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → Result C X ℓ → Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold (res v) o x = o ≡ v → x
unfold (_×∃_ {s = s} af c) o x = af ⊩ᵃᶠ s × ∃[ p ] unfold (c p) o x
unfold (_×∀_ {s = s} af c) o x = af ⊩ᵃᶠ s × ∀ p → unfold (c p) o x

_<_ : {X : Set ℓ} → Rel (List⁺ X) 0ℓ
xs < ys = length⁺ xs <′ length⁺ ys

<-wf : {X : Set ℓ} → WellFounded (_<_ {X = X})
<-wf xs = acc<′⇒acc< (<′-wellFounded (length⁺ xs))
  where
    acc<′⇒acc< : {X : Set ℓ} → {xs : List⁺ X} → Acc _<′_ (length⁺ xs) → Acc _<_ xs
    acc<′⇒acc< (acc h) = acc λ hlt → acc<′⇒acc< (h hlt)

unfold⁺ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → (rs : List⁺ (Result C X ℓ)) → Acc _<_ rs → Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
unfold⁺ (r ∷ []) _ o x = unfold r o x
unfold⁺ (r₁ ∷ r₂ ∷ rs) (acc h) o x = unfold r₁ o x × unfold⁺ (r₂ ∷ rs) (h ≤′-refl) o x

record Container {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (X : Set ℓ₃) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _▷_
  field
    Shape : ℕ
    Position : Fin Shape → C ⋆ X → List⁺ (Result C X ℓ)

open Container

data ModalitySequence (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁) where
  ⟪_⟫_ ⟦_⟧_ : ActionFormula C ℓ → ModalitySequence C ℓ → ModalitySequence C ℓ
  ε : ModalitySequence C ℓ

apply : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → ModalitySequence C ℓ → C ⋆ X → (Maybe' (C ⋆ X) → Result C X ℓ) → Result C X ℓ
apply (⟪ _ ⟫ _) (pure _) f = f fail
apply (⟪ af ⟫ m) (impure (_ , c)) f = af ×∃ λ p → apply m (c p) f
apply (⟦ _ ⟧ _) (pure _) f = f done
apply (⟦ af ⟧ m) (impure (_ , c)) f = af ×∀ λ p → apply m (c p) f
apply ε x f = f (val x)

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
    position m i (val inj₁ x) = apply m i λ { (val _) → res (val inj₁ x) ; done → res done ; fail → res fail }
    position m i (val inj₂ x) = apply m i λ { (val o) → res (val inj₂ (o , x)) ; done → res done ; fail → res fail }
    position m i done = apply m i λ { (val _) → res done ; done → res done ; fail → res fail }
    position m i fail = apply m i λ { (val _) → res fail ; done → res done ; fail → res fail }

extend : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → (Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → (Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
extend {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} {ℓ = ℓ} (val inj₁ x) _ _ = Lift ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) x
extend (val inj₂ (x , fp , _ , _ , _ , p , prev , args)) w m = apply-q (proj₂ (apply-p p args)) prev x (case fp of λ { leastFP → w ; greatestFP → m })
  where
  apply-q : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {X : Set ℓ₃} → {ℓ : Level} → {n : ℕ} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ ⊎ Set ℓ)} → Quantifiedᵈⁿᶠ C ℓ (x ∷ xs) αs → Previous C ℓ (x ∷ xs) → C ⋆ X → (Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  apply-q {X = X} (formulaᵈⁿᶠ d) prev x f = ∃[ s ] ∀ {o} → let rs = Position (containerize d prev X) s x in unfold⁺ rs (<-wf rs) o (f o)
  apply-q (∀ᵈⁿᶠ〔 _ 〕 q) prev x f = ∀ a → apply-q (q a) prev x f
  apply-q (∃ᵈⁿᶠ〔 _ 〕 q) prev x f = ∃[ a ] apply-q (q a) prev x f

  apply-p : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {n : ℕ} → {xs : Vec (List (Set ℓ)) n} → {αs₁ : List (Set ℓ)} → Parameterizedᵈⁿᶠ C ℓ xs αs₁ → Arguments ℓ αs₁ → ∃[ αs₂ ] Quantifiedᵈⁿᶠ C ℓ xs αs₂
  apply-p (quantifiedᵈⁿᶠ_ {αs = αs} q) [] = αs , q
  apply-p (_ ↦ᵈⁿᶠ p) (a ∷ args) = apply-p (p a) args
extend done _ _ = ⊤
extend fail _ _ = ⊥

record W {C : Containerˢᵗᵈ ℓ₁ ℓ₂} ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ {X : Set ℓ₃} {ℓ : Level} (_ : Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs))) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
record M {C : Containerˢᵗᵈ ℓ₁ ℓ₂} ⦃ _ : IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ {X : Set ℓ₃} {ℓ : Level} (_ : Maybe' (Set ℓ ⊎ (C ⋆ X) × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} C ℓ (αs ∷ xs) αs × Previous C ℓ (αs ∷ xs) × Arguments ℓ αs))) : Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

record W i where
  inductive
  constructor wᶜ
  field
    In : extend i W M

record M i where
  coinductive
  constructor mᶜ
  field
    Ni : extend i W M

infix 25 _⊩ᵛ_

_⊩ᵛ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → Formulaᵈⁿᶠ-var C ℓ [] → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
trueᵈⁿᶠ ⊩ᵛ _ = ⊤
falseᵈⁿᶠ ⊩ᵛ _ = ⊥
_⊩ᵛ_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₃} {ℓ = ℓ} (valᵈⁿᶠ x) _ = Lift ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) x
⟨ _ ⟩ᵈⁿᶠ _ ⊩ᵛ pure _ = ⊥
⟨ af ⟩ᵈⁿᶠ v ⊩ᵛ impure (s , c) = af ⊩ᵃᶠ s × ∃[ p ] v ⊩ᵛ c p
[ _ ]ᵈⁿᶠ _ ⊩ᵛ pure _ = ⊤
[ af ]ᵈⁿᶠ v ⊩ᵛ impure (s , c) = af ⊩ᵃᶠ s × ∀ p → v ⊩ᵛ c p
μᵈⁿᶠ_．_ {αs = αs} p args ⊩ᵛ x = W (val inj₂ (x , leastFP , zero , [] , αs , p , 〔 leastFP , p 〕 , args))
νᵈⁿᶠ_．_ {αs = αs} p args ⊩ᵛ x = M (val inj₂ (x , greatestFP , zero , [] , αs , p , 〔 greatestFP , p 〕 , args))

infix 25 _⊩ᶜ_

_⊩ᶜ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → Formulaᵈⁿᶠ-con C ℓ [] → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
con-var v ⊩ᶜ x = v ⊩ᵛ x
v ∧ᵈⁿᶠ c ⊩ᶜ x = (v ⊩ᵛ x) × (c ⊩ᶜ x)

infix 25 _⊩ᵈ_

_⊩ᵈ_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {X : Set ℓ₃} → Formulaᵈⁿᶠ-dis C ℓ [] → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
dis-con c ⊩ᵈ x = c ⊩ᶜ x
c ∨ᵈⁿᶠ d ⊩ᵈ x = (c ⊩ᶜ x) ⊎ (d ⊩ᵈ x)

data Formulaⁱ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)

infix 45 formula_
infix 40 ∀〔_〕_
infix 40 ∃〔_〕_

data Quantifiedⁱ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ ⊎ Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
  formula_ : Formulaⁱ C ℓ xs → Quantifiedⁱ C ℓ xs []
  ∀〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantifiedⁱ C ℓ xs αs) → Quantifiedⁱ C ℓ xs (inj₁ α ∷ αs)
  ∃〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantifiedⁱ C ℓ xs αs) → Quantifiedⁱ C ℓ xs (inj₂ α ∷ αs)

infix 35 quantified_
infix 30 _↦_

data Parameterizedⁱ {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
  quantified_ : ∀ {αs} → Quantifiedⁱ C ℓ xs αs → Parameterizedⁱ C ℓ xs []
  _↦_ : ∀ {αs : List (Set ℓ)} → (α : Set ℓ) → (α → Parameterizedⁱ C ℓ xs αs) → Parameterizedⁱ C ℓ xs (α ∷ αs)

infix 80 val_
infix 80 ref_．_
infix 75 ¬_
infix 70 ⟨_⟩_
infix 70 [_]_
infixr 65 _∧_
infixr 60 _∨_
infixr 55 _⇒_
infix 50 μ_．_
infix 50 ν_．_

data Formulaⁱ C ℓ where
  true false : ∀ {xs} → Formulaⁱ C ℓ xs
  val_ : ∀ {xs} → Set ℓ → Formulaⁱ C ℓ xs
  ¬_ : ∀ {xs} → Formulaⁱ C ℓ xs → Formulaⁱ C ℓ xs
  _∧_ _∨_ _⇒_ : ∀ {xs} → Formulaⁱ C ℓ xs → Formulaⁱ C ℓ xs → Formulaⁱ C ℓ xs
  ⟨_⟩_ [_]_ : ∀ {xs} → RegularFormula C ℓ → Formulaⁱ C ℓ xs → Formulaⁱ C ℓ xs
  μ_．_ ν_．_ : ∀ {αs xs} → Parameterizedⁱ C ℓ (αs ∷ xs) αs → Arguments ℓ αs → Formulaⁱ C ℓ xs
  ref_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ (lookupᵛ xs i) → Formulaⁱ C ℓ xs

Formula : (C : Containerˢᵗᵈ ℓ₁ ℓ₂) → (ℓ : Level) → (αs : List (Set ℓ ⊎ Set ℓ)) → Set ((sucˡ ℓ) ⊔ ℓ₁)
Formula C ℓ αs = Quantifiedⁱ C ℓ [] αs

infix 25 _⊩_

_⊩_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {αs : List (Set ℓ ⊎ Set ℓ)} → {X : Set ℓ₃} → Formula C ℓ αs → C ⋆ X → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
∀〔 _ 〕 qⁱ ⊩ x = ∀ a → qⁱ a ⊩ x
∃〔 _ 〕 qⁱ ⊩ x = ∃[ a ] qⁱ a ⊩ x
formula fⁱ ⊩ x = f''→fᵈⁿᶠ (f'→f'' (fⁱ→f' fⁱ)) ⊩ᵈ x
  where
  infix 100 actF'_
  infix 95 _*'
  infixr 90 _·'_
  infixr 85 _+'_

  data RegularFormula' (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Set ((sucˡ ℓ) ⊔ ℓ₁) where
    ε' : RegularFormula' C ℓ
    actF'_ : ActionFormula C ℓ → RegularFormula' C ℓ
    _·'_ _+'_ : RegularFormula' C ℓ → RegularFormula' C ℓ → RegularFormula' C ℓ
    _*' : RegularFormula' C ℓ → RegularFormula' C ℓ

  rf→rf' : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → RegularFormula C ℓ → RegularFormula' C ℓ
  rf→rf' ε = ε'
  rf→rf' (actF af) = actF' af
  rf→rf' (rf₁ · rf₂) = rf→rf' rf₁ ·' rf→rf' rf₂
  rf→rf' (rf₁ + rf₂) = rf→rf' rf₁ +' rf→rf' rf₂
  rf→rf' (rf *) = rf→rf' rf *'
  rf→rf' {C = C} {ℓ = ℓ} (rf ⁺) = rf' ·' (rf' *')
    where
    rf' : RegularFormula' C ℓ
    rf' = rf→rf' rf

  data Formula' {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)

  infix 45 formula'_
  infix 40 ∀'〔_〕_
  infix 40 ∃'〔_〕_

  data Quantified' {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ ⊎ Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
    formula'_ : Formula' C ℓ xs → Quantified' C ℓ xs []
    ∀'〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantified' C ℓ xs αs) → Quantified' C ℓ xs (inj₁ α ∷ αs)
    ∃'〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantified' C ℓ xs αs) → Quantified' C ℓ xs (inj₂ α ∷ αs)

  infix 35 quantified'_
  infix 30 _↦'_

  data Parameterized' {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
    quantified'_ : ∀ {αs} → Quantified' C ℓ xs αs → Parameterized' C ℓ xs []
    _↦'_ : ∀ {αs : List (Set ℓ)} → (α : Set ℓ) → (α → Parameterized' C ℓ xs αs) → Parameterized' C ℓ xs (α ∷ αs)

  infix 80 val'_
  infix 80 ref'_．_
  infix 75 ¬'_
  infix 70 ⟨_⟩'_
  infix 70 [_]'_
  infixr 65 _∧'_
  infixr 60 _∨'_
  infixr 55 _⇒'_
  infix 50 μ'_．_
  infix 50 ν'_．_

  data Formula' C ℓ where
    true' false' : ∀ {xs} → Formula' C ℓ xs
    val'_ : ∀ {xs} → Set ℓ → Formula' C ℓ xs
    ¬'_ : ∀ {xs} → Formula' C ℓ xs → Formula' C ℓ xs
    _∧'_ _∨'_ _⇒'_ : ∀ {xs} → Formula' C ℓ xs → Formula' C ℓ xs → Formula' C ℓ xs
    ⟨_⟩'_ [_]'_ : ∀ {xs} → ActionFormula C ℓ → Formula' C ℓ xs → Formula' C ℓ xs
    μ'_．_ ν'_．_ : ∀ {αs xs} → Parameterized' C ℓ (αs ∷ xs) αs → Arguments ℓ αs → Formula' C ℓ xs
    ref'_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ (lookupᵛ xs i) → Formula' C ℓ xs

  ref⁺ : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {x : List (Set ℓ)} → {xs : Vec (List (Set ℓ)) n} → Formula' C ℓ xs → Formula' C ℓ (x ∷ xs)
  ref⁺ f' = ref⁺' {xs₁ = []} f'
    where
    ref⁺' : {n₁ n₂ : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {x : List (Set ℓ)} → {xs₁ : Vec (List (Set ℓ)) n₁} → {xs₂ : Vec (List (Set ℓ)) n₂} → Formula' C ℓ (xs₁ ++ xs₂) → Formula' C ℓ (xs₁ ++ x ∷ xs₂)

    ref⁺'-q : {n₁ n₂ : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {x : List (Set ℓ)} → {xs₁ : Vec (List (Set ℓ)) n₁} → {xs₂ : Vec (List (Set ℓ)) n₂} → {αs : List (Set ℓ ⊎ Set ℓ)} → Quantified' C ℓ (xs₁ ++ xs₂) αs → Quantified' C ℓ (xs₁ ++ x ∷ xs₂) αs
    ref⁺'-q (formula' f') = formula' ref⁺' f'
    ref⁺'-q (∀'〔 α 〕 q') = ∀'〔 α 〕 λ a → ref⁺'-q (q' a)
    ref⁺'-q (∃'〔 α 〕 q') = ∃'〔 α 〕 λ a → ref⁺'-q (q' a)

    ref⁺'-p : {n₁ n₂ : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {x : List (Set ℓ)} → {xs₁ : Vec (List (Set ℓ)) n₁} → {xs₂ : Vec (List (Set ℓ)) n₂} → {αs : List (Set ℓ)} → Parameterized' C ℓ (xs₁ ++ xs₂) αs → Parameterized' C ℓ (xs₁ ++ x ∷ xs₂) αs
    ref⁺'-p (quantified' q') = quantified' ref⁺'-q q'
    ref⁺'-p (α ↦' p') = α ↦' λ a → ref⁺'-p (p' a)

    ref⁺' true' = true'
    ref⁺' false' = false'
    ref⁺' (val' x) = val' x
    ref⁺' (¬' f') = ¬' ref⁺' f'
    ref⁺' (f'₁ ∧' f'₂) = ref⁺' f'₁ ∧' ref⁺' f'₂
    ref⁺' (f'₁ ∨' f'₂) = ref⁺' f'₁ ∨' ref⁺' f'₂
    ref⁺' (f'₁ ⇒' f'₂) = ref⁺' f'₁ ⇒' ref⁺' f'₂
    ref⁺' (⟨ af ⟩' f') = ⟨ af ⟩' ref⁺' f'
    ref⁺' ([ af ]' f') = [ af ]' ref⁺' f'
    ref⁺' {xs₁ = xs₁} (μ'_．_ {αs = αs} p' args) = μ'_．_ (ref⁺'-p {xs₁ = αs ∷ xs₁} p') args
    ref⁺' {xs₁ = xs₁} (ν'_．_ {αs = αs} p' args) = ν'_．_ (ref⁺'-p {xs₁ = αs ∷ xs₁} p') args
    ref⁺' {n₁ = n₁} {ℓ = l} {x = x} {xs₁ = xs₁} {xs₂ = xs₂} (ref' i ． args) with toℕ i <ᵇ n₁ | inspect (_<ᵇ_ (toℕ i)) n₁
    ... | false | [ hn ]⁼ = ref' i' i ． subst (Arguments l) (hlookup x xs₁ xs₂ i (≮⇒≥ λ h → subst T hn (<⇒<ᵇ h))) args
      where
      i' : {n₁ n₂ : ℕ} → Fin (n₁ ＋ n₂) → Fin (n₁ ＋ suc n₂)
      i' {n₁ = n₁} {n₂ = n₂} i = cast (sym (+-suc n₁ n₂)) (suc i)

      hlookup : {α : Set ℓ} → {n₁ n₂ : ℕ} → (x : α) → (xs₁ : Vec α n₁) → (xs₂ : Vec α n₂) → (i : Fin (n₁ ＋ n₂)) → toℕ i ≥ n₁ → lookupᵛ (xs₁ ++ xs₂) i ≡ lookupᵛ (xs₁ ++ x ∷ xs₂) (i' i)
      hlookup _ [] _ zero _ = refl
      hlookup x [] (_ ∷ xs₂) (suc i) z≤n = hlookup x [] xs₂ i z≤n
      hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h
    ... | true | [ h ]⁼ = ref' i' i ． subst (Arguments l) (hlookup x xs₁ xs₂ i (<ᵇ⇒< (toℕ i) n₁ (subst T (sym h) tt))) args
      where
      i' : {n₁ n₂ : ℕ} → Fin (n₁ ＋ n₂) → Fin (n₁ ＋ suc n₂)
      i' {n₁ = n₁} {n₂ = n₂} i = cast (sym (+-suc n₁ n₂)) (inject₁ i)

      hlookup : {α : Set ℓ} → {n₁ n₂ : ℕ} → (x : α) → (xs₁ : Vec α n₁) → (xs₂ : Vec α n₂) → (i : Fin (n₁ ＋ n₂)) → toℕ i <ⁿ n₁ → lookupᵛ (xs₁ ++ xs₂) i ≡ lookupᵛ (xs₁ ++ x ∷ xs₂) (i' i)
      hlookup _ (_ ∷ _) _ zero _ = refl
      hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h

  fⁱ→f' : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formulaⁱ C ℓ xs → Formula' C ℓ xs

  qⁱ→q' : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ ⊎ Set ℓ)} → Quantifiedⁱ C ℓ xs αs → Quantified' C ℓ xs αs
  qⁱ→q' (formula fⁱ) = formula' fⁱ→f' fⁱ
  qⁱ→q' (∀〔 α 〕 qⁱ) = ∀'〔 α 〕 λ a → qⁱ→q' (qⁱ a)
  qⁱ→q' (∃〔 α 〕 qⁱ) = ∃'〔 α 〕 λ a → qⁱ→q' (qⁱ a)

  pⁱ→p' : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterizedⁱ C ℓ xs αs → Parameterized' C ℓ xs αs
  pⁱ→p' (quantified qⁱ) = quantified' qⁱ→q' qⁱ
  pⁱ→p' (α ↦ pⁱ) = α ↦' λ a → pⁱ→p' (pⁱ a)

  fⁱ→f' true = true'
  fⁱ→f' false = false'
  fⁱ→f' (val x) = val' x
  fⁱ→f' (¬ fⁱ) = ¬' fⁱ→f' fⁱ
  fⁱ→f' (fⁱ₁ ∧ fⁱ₂) = fⁱ→f' fⁱ₁ ∧' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ∨ fⁱ₂) = fⁱ→f' fⁱ₁ ∨' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ⇒ fⁱ₂) = fⁱ→f' fⁱ₁ ⇒' fⁱ→f' fⁱ₂
  fⁱ→f' (⟨ rf ⟩ fⁱ) = helper-∃ (rf→rf' rf) (fⁱ→f' fⁱ)
    where
    helper-∃ : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → RegularFormula' C ℓ → Formula' C ℓ xs → Formula' C ℓ xs
    helper-∃ ε' f' = f'
    helper-∃ (actF' af) f' = ⟨ af ⟩' f'
    helper-∃ (rf'₁ ·' rf'₂) f' = helper-∃ rf'₁ (helper-∃ rf'₂ f')
    helper-∃ (rf'₁ +' rf'₂) f' = helper-∃ rf'₁ f' ∨' helper-∃ rf'₂ f'
    helper-∃ (rf' *') f' = μ' quantified' (formula' (helper-∃ rf' (ref' zero ． []) ∨' ref⁺ f')) ． []
  fⁱ→f' ([ rf ] fⁱ) = helper-∀ (rf→rf' rf) (fⁱ→f' fⁱ)
    where
    helper-∀ : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → RegularFormula' C ℓ → Formula' C ℓ xs → Formula' C ℓ xs
    helper-∀ ε' f' = f'
    helper-∀ (actF' af) f' = [ af ]' f'
    helper-∀ (rf'₁ ·' rf'₂) f' = helper-∀ rf'₁ (helper-∀ rf'₂ f')
    helper-∀ (rf'₁ +' rf'₂) f' = helper-∀ rf'₁ f' ∨' helper-∀ rf'₂ f'
    helper-∀ (rf' *') f' = ν' quantified' (formula' (helper-∀ rf' (ref' zero ． []) ∨' ref⁺ f')) ． []
  fⁱ→f' (μ pⁱ ． args) = μ' pⁱ→p' pⁱ ． args
  fⁱ→f' (ν pⁱ ． args) = ν' pⁱ→p' pⁱ ． args
  fⁱ→f' (ref i ． args) = ref' i ． args

  data Formula'' {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) : Vec (List (Set ℓ)) n → Set ((sucˡ ℓ) ⊔ ℓ₁)

  infix 45 formula''_
  infix 40 ∀''〔_〕_
  infix 40 ∃''〔_〕_

  data Quantified'' {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ ⊎ Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
    formula''_ : Formula'' C ℓ xs → Quantified'' C ℓ xs []
    ∀''〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantified'' C ℓ xs αs) → Quantified'' C ℓ xs (inj₁ α ∷ αs)
    ∃''〔_〕_ : ∀ {α αs} → Inhabited α → (α → Quantified'' C ℓ xs αs) → Quantified'' C ℓ xs (inj₂ α ∷ αs)

  infix 35 quantified''_
  infix 30 _↦''_

  data Parameterized'' {n : ℕ} (C : Containerˢᵗᵈ ℓ₁ ℓ₂) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set ((sucˡ ℓ) ⊔ ℓ₁) where
    quantified''_ : ∀ {αs} → Quantified'' C ℓ xs αs → Parameterized'' C ℓ xs []
    _↦''_ : ∀ {αs : List (Set ℓ)} → (α : Set ℓ) → (α → Parameterized'' C ℓ xs αs) → Parameterized'' C ℓ xs (α ∷ αs)

  infix 80 val''_
  infix 80 ref''〔_〕_．_
  infix 70 ⟨_⟩''_
  infix 70 [_]''_
  infixr 65 _∧''_
  infixr 60 _∨''_
  infix 50 μ''_．_
  infix 50 ν''_．_

  data Formula'' C ℓ where
    true'' false'' : ∀ {xs} → Formula'' C ℓ xs
    val''_ : ∀ {xs} → Set ℓ → Formula'' C ℓ xs
    _∧''_ _∨''_ : ∀ {xs} → Formula'' C ℓ xs → Formula'' C ℓ xs → Formula'' C ℓ xs
    ⟨_⟩''_ [_]''_ : ∀ {xs} → ActionFormula C ℓ → Formula'' C ℓ xs → Formula'' C ℓ xs
    μ''_．_ ν''_．_ : ∀ {αs xs} → Parameterized'' C ℓ (αs ∷ xs) αs → Arguments ℓ αs → Formula'' C ℓ xs
    ref''〔_〕_．_ : ∀ {xs} → Bool → (i : Fin (lengthᵛ xs)) → Arguments ℓ (lookupᵛ xs i) → Formula'' C ℓ xs

  flipRef : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Fin n → Formula'' C ℓ xs → Formula'' C ℓ xs

  flipRef-q : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ ⊎ Set ℓ)} → Fin n → Quantified'' C ℓ xs αs → Quantified'' C ℓ xs αs
  flipRef-q x (formula'' f'') = formula'' flipRef x f''
  flipRef-q x (∀''〔 α 〕 q'') = ∀''〔 α 〕 λ a → flipRef-q x (q'' a)
  flipRef-q x (∃''〔 α 〕 q'') = ∃''〔 α 〕 λ a → flipRef-q x (q'' a)

  flipRef-p : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ)} → Fin n → Parameterized'' C ℓ xs αs → Parameterized'' C ℓ xs αs
  flipRef-p x (quantified'' q'') = quantified'' flipRef-q x q''
  flipRef-p x (α ↦'' p'') = α ↦'' λ a → flipRef-p x (p'' a)

  flipRef _ true'' = true''
  flipRef _ false'' = false''
  flipRef _ (val'' x) = val'' x
  flipRef x (f''₁ ∧'' f''₂) = flipRef x f''₁ ∧'' flipRef x f''₂
  flipRef x (f''₁ ∨'' f''₂) = flipRef x f''₁ ∨'' flipRef x f''₂
  flipRef x (⟨ af ⟩'' f'') = ⟨ af ⟩'' flipRef x f''
  flipRef x ([ af ]'' f'') = [ af ]'' flipRef x f''
  flipRef x (μ'' p'' ． args) = μ'' flipRef-p (suc x) p'' ． args
  flipRef x (ν'' p'' ． args) = ν'' flipRef-p (suc x) p'' ． args
  flipRef x (ref''〔 b 〕 i ． args) with i ≟ᶠ x
  ... | no _ = ref''〔 b 〕 i ． args
  ... | yes _ = ref''〔 not b 〕 i ． args

  negate : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formula'' C ℓ xs → Formula'' C ℓ xs
  negate true'' = false''
  negate false'' = true''
  negate (val'' x) = val'' (¬ˢᵗᵈ x)
  negate (f''₁ ∧'' f''₂) = negate f''₁ ∨'' negate f''₂
  negate (f''₁ ∨'' f''₂) = negate f''₁ ∧'' negate f''₂
  negate (⟨ af ⟩'' f'') = [ af ]'' negate f''
  negate ([ af ]'' f'') = ⟨ af ⟩'' negate f''
  negate (μ'' p'' ． args) = ν'' flipRef-p zero p'' ． args
  negate (ν'' p'' ． args) = μ'' flipRef-p zero p'' ． args
  negate (ref''〔 b 〕 i ． args) = ref''〔 not b 〕 i ． args

  f'→f'' : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formula' C ℓ xs → Formula'' C ℓ xs

  q'→q'' : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ ⊎ Set ℓ)} → Quantified' C ℓ xs αs → Quantified'' C ℓ xs αs
  q'→q'' (formula' f') = formula'' f'→f'' f'
  q'→q'' (∀'〔 α 〕 q') = ∀''〔 α 〕 λ a → q'→q'' (q' a)
  q'→q'' (∃'〔 α 〕 q') = ∃''〔 α 〕 λ a → q'→q'' (q' a)

  p'→p'' : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterized' C ℓ xs αs → Parameterized'' C ℓ xs αs
  p'→p'' (quantified' q') = quantified'' q'→q'' q'
  p'→p'' (α ↦' p') = α ↦'' λ a → p'→p'' (p' a)

  f'→f'' true' = true''
  f'→f'' false' = false''
  f'→f'' (val' x) = val'' x
  f'→f'' (¬' f') = negate (f'→f'' f')
  f'→f'' (f'₁ ∧' f'₂) = f'→f'' f'₁ ∧'' f'→f'' f'₂
  f'→f'' (f'₁ ∨' f'₂) = f'→f'' f'₁ ∨'' f'→f'' f'₂
  f'→f'' (f'₁ ⇒' f'₂) = negate (f'→f'' f'₁) ∨'' f'→f'' f'₂
  f'→f'' (⟨ af ⟩' f') = ⟨ af ⟩'' f'→f'' f'
  f'→f'' ([ af ]' f') = [ af ]'' f'→f'' f'
  f'→f'' (μ' p' ． args) = μ'' p'→p'' p' ． args
  f'→f'' (ν' p' ． args) = ν'' p'→p'' p' ． args
  f'→f'' (ref' i ． args) = ref''〔 true 〕 i ． args

  merge-dis-dis-or : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs
  merge-dis-dis-or (dis-con c) d = c ∨ᵈⁿᶠ d
  merge-dis-dis-or (c ∨ᵈⁿᶠ d₁) d₂ = c ∨ᵈⁿᶠ merge-dis-dis-or d₁ d₂

  merge-con-con : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs
  merge-con-con (con-var v) c = v ∧ᵈⁿᶠ c
  merge-con-con (v ∧ᵈⁿᶠ c₁) c₂ = v ∧ᵈⁿᶠ merge-con-con c₁ c₂

  merge-con-dis : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs
  merge-con-dis c₁ (dis-con c₂) = dis-con (merge-con-con c₁ c₂)
  merge-con-dis c₁ (c₂ ∨ᵈⁿᶠ d₂) = merge-con-con c₁ c₂ ∨ᵈⁿᶠ merge-con-dis c₁ d₂

  merge-dis-dis-and : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs
  merge-dis-dis-and (dis-con c) d = merge-con-dis c d
  merge-dis-dis-and (c ∨ᵈⁿᶠ d₁) d₂ = merge-dis-dis-or (merge-con-dis c d₂) (merge-dis-dis-and d₁ d₂)

  f''→fᵈⁿᶠ : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → Formula'' C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs

  q''→qᵈⁿᶠ : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ ⊎ Set ℓ)} → Quantified'' C ℓ xs αs → Quantifiedᵈⁿᶠ C ℓ xs αs
  q''→qᵈⁿᶠ (formula'' f'') = formulaᵈⁿᶠ f''→fᵈⁿᶠ f''
  q''→qᵈⁿᶠ (∀''〔 α 〕 q'') = ∀ᵈⁿᶠ〔 α 〕 λ a → q''→qᵈⁿᶠ (q'' a)
  q''→qᵈⁿᶠ (∃''〔 α 〕 q'') = ∃ᵈⁿᶠ〔 α 〕 λ a → q''→qᵈⁿᶠ (q'' a)

  p''→pᵈⁿᶠ : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterized'' C ℓ xs αs → Parameterizedᵈⁿᶠ C ℓ xs αs
  p''→pᵈⁿᶠ (quantified'' q'') = quantifiedᵈⁿᶠ q''→qᵈⁿᶠ q''
  p''→pᵈⁿᶠ (α ↦'' p'') = α ↦ᵈⁿᶠ λ a → p''→pᵈⁿᶠ (p'' a)

  f''→fᵈⁿᶠ true'' = dis-con con-var trueᵈⁿᶠ
  f''→fᵈⁿᶠ false'' = dis-con con-var falseᵈⁿᶠ
  f''→fᵈⁿᶠ (val'' x) = dis-con con-var valᵈⁿᶠ x
  f''→fᵈⁿᶠ (f''₁ ∧'' f''₂) = merge-dis-dis-and (f''→fᵈⁿᶠ f''₁) (f''→fᵈⁿᶠ f''₂)
  f''→fᵈⁿᶠ (f''₁ ∨'' f''₂) = merge-dis-dis-or (f''→fᵈⁿᶠ f''₁) (f''→fᵈⁿᶠ f''₂)
  f''→fᵈⁿᶠ (⟨ af ⟩'' f'') = merge-∃-dis af (f''→fᵈⁿᶠ f'')
    where
    merge-∃-var : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → ActionFormula C ℓ → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-var C ℓ xs
    merge-∃-var af v = ⟨ af ⟩ᵈⁿᶠ v

    merge-∃-con : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → ActionFormula C ℓ → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs
    merge-∃-con af (con-var v) = con-var (merge-∃-var af v)
    merge-∃-con af (v ∧ᵈⁿᶠ c) = merge-∃-var af v ∧ᵈⁿᶠ merge-∃-con af c

    merge-∃-dis : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → ActionFormula C ℓ → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs
    merge-∃-dis af (dis-con c) = dis-con (merge-∃-con af c)
    merge-∃-dis af (c ∨ᵈⁿᶠ d) = merge-∃-con af c ∨ᵈⁿᶠ merge-∃-dis af d
  f''→fᵈⁿᶠ ([ af ]'' f'') = merge-∀-dis af (f''→fᵈⁿᶠ f'')
    where
    merge-∀-var : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → ActionFormula C ℓ → Formulaᵈⁿᶠ-var C ℓ xs → Formulaᵈⁿᶠ-var C ℓ xs
    merge-∀-var af v = [ af ]ᵈⁿᶠ v

    merge-∀-con : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → ActionFormula C ℓ → Formulaᵈⁿᶠ-con C ℓ xs → Formulaᵈⁿᶠ-con C ℓ xs
    merge-∀-con af (con-var v) = con-var (merge-∀-var af v)
    merge-∀-con af (v ∧ᵈⁿᶠ c) = merge-∀-var af v ∧ᵈⁿᶠ merge-∀-con af c

    merge-∀-dis : {n : ℕ} → {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → ActionFormula C ℓ → Formulaᵈⁿᶠ-dis C ℓ xs → Formulaᵈⁿᶠ-dis C ℓ xs
    merge-∀-dis af (dis-con c) = dis-con (merge-∀-con af c)
    merge-∀-dis af (c ∨ᵈⁿᶠ d) = merge-∀-con af c ∨ᵈⁿᶠ merge-∀-dis af d
  f''→fᵈⁿᶠ (μ'' p'' ． args) = dis-con con-var μᵈⁿᶠ p''→pᵈⁿᶠ p'' ． args
  f''→fᵈⁿᶠ (ν'' p'' ． args) = dis-con con-var νᵈⁿᶠ p''→pᵈⁿᶠ p'' ． args
  f''→fᵈⁿᶠ (ref''〔 false 〕 i ． args) = dis-con con-var falseᵈⁿᶠ
  f''→fᵈⁿᶠ (ref''〔 true 〕 i ． args) = dis-con con-var refᵈⁿᶠ i ． args

infix 25 _⊩_!_

_⊩_!_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {αs : List (Set ℓ ⊎ Set ℓ)} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C ℓ αs → Program C I O → I → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
f ⊩ x ! i = f ⊩ x i

infix 25 _▸_⊩_!_

_▸_⊩_!_ : {C : Containerˢᵗᵈ ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shapeˢᵗᵈ C} _≡_ ⦄ → {ℓ : Level} → {αs : List (Set ℓ ⊎ Set ℓ)} → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula C ℓ αs → RecursiveProgram C I O → I → Set ((sucˡ ℓ) ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
n ▸ f ⊩ x ! i = f ⊩ (recursionHandler x n) i
