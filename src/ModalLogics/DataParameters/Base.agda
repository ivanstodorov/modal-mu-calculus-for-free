{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.DataParameters.Base where

open import Common.Program using (Program; free; pure; impure)
open import Data.Bool using (Bool; not; T)
open import Data.Container using (Container)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; toℕ; inject₁; cast) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List) renaming (lookup to lookup')
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷⁺_; foldr; toList) renaming (length to length⁺)
open import Data.Nat using (ℕ; _<ᵇ_; _<′_; ≤′-refl; z≤n; s≤s; _≥_) renaming (_+_ to _＋_; _<_ to _<ⁿ_)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Nat.Properties using (+-suc; <ᵇ⇒<; <⇒<ᵇ; ≮⇒≥)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; _++_) renaming (length to lengthᵛ; [_] to [_]ᵛ; lookup to lookupᵛ)
open import Function using (case_of_)
open import Induction.WellFounded using (WellFounded; Acc)
open import Level using (Level; 0ℓ; _⊔_; Lift) renaming (suc to sucˡ)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; RegularFormula; _∈_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; subst; sym) renaming ([_] to [_]⁼)
open import Relation.Nullary using (¬_; yes; no)

open Bool
open Container
open Fin
open List
open ℕ
open _⊎_
open Vec
open Acc
open RegularFormula
open _≡_

private variable
  ℓ ℓₛ ℓₚ ℓₓ ℓ₁ : Level

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {α αs} → α → Arguments ℓ αs → Arguments ℓ (α ∷ αs)

data Formulaᵈⁿᶠ-var {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) : Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁))
data Formulaᵈⁿᶠ-con {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) : Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁))
data Formulaᵈⁿᶠ-dis {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) : Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁))

infix 45 formulaᵈⁿᶠ_
infix 40 ∀ᵈⁿᶠ〔_〕_
infix 40 ∃ᵈⁿᶠ〔_〕_

data Quantifiedᵈⁿᶠ {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁ ⊎ Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
  formulaᵈⁿᶠ_ : Formulaᵈⁿᶠ-dis S ℓ₁ xs → Quantifiedᵈⁿᶠ S ℓ₁ xs []
  ∀ᵈⁿᶠ〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantifiedᵈⁿᶠ S ℓ₁ xs αs) → Quantifiedᵈⁿᶠ S ℓ₁ xs (inj₁ α ∷ αs)
  ∃ᵈⁿᶠ〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantifiedᵈⁿᶠ S ℓ₁ xs αs) → Quantifiedᵈⁿᶠ S ℓ₁ xs (inj₂ α ∷ αs)

infix 35 quantifiedᵈⁿᶠ_
infix 30 _↦ᵈⁿᶠ_

data Parameterizedᵈⁿᶠ {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
  quantifiedᵈⁿᶠ_ : ∀ {αs} → Quantifiedᵈⁿᶠ S ℓ₁ xs αs → Parameterizedᵈⁿᶠ S ℓ₁ xs []
  _↦ᵈⁿᶠ_ : ∀ {αs : List (Set ℓ₁)} → (α : Set ℓ₁) → (α → Parameterizedᵈⁿᶠ S ℓ₁ xs αs) → Parameterizedᵈⁿᶠ S ℓ₁ xs (α ∷ αs)

infix 80 valᵈⁿᶠ_
infix 80 refᵈⁿᶠ_．_
infix 75 ⟨_⟩ᵈⁿᶠ_
infix 75 [_]ᵈⁿᶠ_
infix 70 μᵈⁿᶠ_．_
infix 70 νᵈⁿᶠ_．_

data Formulaᵈⁿᶠ-var S ℓ₁ where
  trueᵈⁿᶠ falseᵈⁿᶠ : ∀ {xs} → Formulaᵈⁿᶠ-var S ℓ₁ xs
  valᵈⁿᶠ_ : ∀ {xs} → Set ℓ₁ → Formulaᵈⁿᶠ-var S ℓ₁ xs
  ⟨_⟩ᵈⁿᶠ_ [_]ᵈⁿᶠ_ : ∀ {xs} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-var S ℓ₁ xs → Formulaᵈⁿᶠ-var S ℓ₁ xs
  μᵈⁿᶠ_．_ νᵈⁿᶠ_．_ : ∀ {αs xs} → Parameterizedᵈⁿᶠ S ℓ₁ (αs ∷ xs) αs → Arguments ℓ₁ αs → Formulaᵈⁿᶠ-var S ℓ₁ xs
  refᵈⁿᶠ_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ₁ (lookupᵛ xs i) → Formulaᵈⁿᶠ-var S ℓ₁ xs

infix 65 con-var_
infixr 60 _∧ᵈⁿᶠ_

data Formulaᵈⁿᶠ-con S ℓ₁ where
  con-var_ : ∀ {xs} → Formulaᵈⁿᶠ-var S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs
  _∧ᵈⁿᶠ_ : ∀ {xs} → Formulaᵈⁿᶠ-var S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs

infix 55 dis-con_
infixr 50 _∨ᵈⁿᶠ_

data Formulaᵈⁿᶠ-dis S ℓ₁ where
  dis-con_ : ∀ {xs} → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs
  _∨ᵈⁿᶠ_ : ∀ {xs} → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs

data FixedPoint : Set where
  leastFP : FixedPoint
  greatestFP : FixedPoint

data Previous (S : Set ℓ) (ℓ₁ : Level) : {n : ℕ} → Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁)) where
  〔_〕 : ∀ {αs : List (Set ℓ₁)} → FixedPoint × Parameterizedᵈⁿᶠ S ℓ₁ [ αs ]ᵛ αs → Previous S ℓ₁ [ αs ]ᵛ
  _∷_ : ∀ {αs : List (Set ℓ₁)} {n : ℕ} {xs : Vec (List (Set ℓ₁)) n} → FixedPoint × Parameterizedᵈⁿᶠ S ℓ₁ (αs ∷ xs) αs → Previous S ℓ₁ xs → Previous S ℓ₁ (αs ∷ xs)

lookup : {S : Set ℓ} → {ℓ₁ : Level} → {n₁ : ℕ} → {xs₁ : Vec (List (Set ℓ₁)) n₁} → Previous S ℓ₁ xs₁ → (i : Fin n₁) → FixedPoint × ∃[ n₂ ] ∃[ xs₂ ] Parameterizedᵈⁿᶠ {n = suc n₂} S ℓ₁ ((lookupᵛ xs₁ i) ∷ xs₂) (lookupᵛ xs₁ i) × Previous S ℓ₁ ((lookupᵛ xs₁ i) ∷ xs₂)
lookup {xs₁ = αs ∷ []} prev@(〔 fp , p 〕) zero = fp , zero , [] , p , prev
lookup {n₁ = suc n} {xs₁ = αs ∷ xs} prev@((fp , p) ∷ _) zero = fp , n , xs , p , prev
lookup (_ ∷ prev) (suc i) = lookup prev i

data Maybe' (α : Set ℓ) : Set ℓ where
  val_ : α → Maybe' α
  done : Maybe' α
  fail : Maybe' α

data Result (C : Container ℓₛ ℓₚ) (X : Set ℓₓ) (ℓ₁ : Level) : Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁)) where
  res_ : Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Result C X ℓ₁
  _×∃_ : ∀ {s} → ActionFormula (Shape C) ℓ₁ → (Position C s → Result C X ℓ₁) → Result C X ℓ₁
  _×∀_ : ∀ {s} → ActionFormula (Shape C) ℓ₁ → (Position C s → Result C X ℓ₁) → Result C X ℓ₁

unfold : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → Result C X ℓ₁ → Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
unfold (res v) o x = o ≡ v → x
unfold (_×∃_ {s = s} af c) o x = s ∈ af × ∃[ p ] unfold (c p) o x
unfold (_×∀_ {s = s} af c) o x = s ∈ af → ∀ p → unfold (c p) o x

_<_ : {X : Set ℓ} → Rel (List⁺ X) 0ℓ
xs < ys = length⁺ xs <′ length⁺ ys

<-wf : {X : Set ℓ} → WellFounded (_<_ {X = X})
<-wf xs = acc<′⇒acc< (<′-wellFounded (length⁺ xs))
  where
    acc<′⇒acc< : {X : Set ℓ} → {xs : List⁺ X} → Acc _<′_ (length⁺ xs) → Acc _<_ xs
    acc<′⇒acc< (acc h) = acc λ hlt → acc<′⇒acc< (h hlt)

unfold⁺ : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → (rs : List⁺ (Result C X ℓ₁)) → Acc _<_ rs → Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
unfold⁺ (r ∷ []) _ o x = unfold r o x
unfold⁺ (r₁ ∷ r₂ ∷ rs) (acc h) o x = unfold r₁ o x × unfold⁺ (r₂ ∷ rs) (h ≤′-refl) o x

record Containerⁱ {n : ℕ} (C : Container ℓₛ ℓₚ) (X : Set ℓₓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁)) where
  constructor _▷_
  field
    Shapeⁱ : ℕ
    Positionⁱ : Fin Shapeⁱ → Program C X → List⁺ (Result C X ℓ₁)

open Containerⁱ

data ModalitySequence (S : Set ℓ) (ℓ₁ : Level) : Set (ℓ ⊔ (sucˡ ℓ₁)) where
  ⟪_⟫_ ⟦_⟧_ : ActionFormula S ℓ₁ → ModalitySequence S ℓ₁ → ModalitySequence S ℓ₁
  ε : ModalitySequence S ℓ₁

apply : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → ModalitySequence (Shape C) ℓ₁ → Program C X → (Maybe' (Program C X) → Result C X ℓ₁) → Result C X ℓ₁
apply (⟪ af ⟫ m) x f with free x
... | pure _ = f fail
... | impure (_ , c) = af ×∃ λ p → apply m (c p) f
apply (⟦ af ⟧ m) x f with free x
... | pure _ = f done
... | impure (_ , c) = af ×∀ λ p → apply m (c p) f
apply ε x f = f (val x)

containerize-var : {S : Set ℓ} → {ℓ₁ : Level} → {n : ℕ} → {x : List (Set ℓ₁)} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-var S ℓ₁ (x ∷ xs) → Previous S ℓ₁ (x ∷ xs) → ModalitySequence S ℓ₁ × Maybe' (Set ℓ₁ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} S ℓ₁ (αs ∷ xs) αs × Previous S ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs))
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

containerize-con : {S : Set ℓ} → {ℓ₁ : Level} → {n : ℕ} → {x : List (Set ℓ₁)} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-con S ℓ₁ (x ∷ xs) → Previous S ℓ₁ (x ∷ xs) → List⁺ (ModalitySequence S ℓ₁ × Maybe' (Set ℓ₁ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} S ℓ₁ (αs ∷ xs) αs × Previous S ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)))
containerize-con (con-var v) prev = [ containerize-var v prev ]
containerize-con (v ∧ᵈⁿᶠ c) prev = containerize-var v prev ∷⁺ containerize-con c prev

containerize-dis : {S : Set ℓ} → {ℓ₁ : Level} → {n : ℕ} → {x : List (Set ℓ₁)} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-dis S ℓ₁ (x ∷ xs) → Previous S ℓ₁ (x ∷ xs) → List⁺ (List⁺ (ModalitySequence S ℓ₁ × Maybe' (Set ℓ₁ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} S ℓ₁ (αs ∷ xs) αs × Previous S ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs))))
containerize-dis (dis-con c) prev = [ containerize-con c prev ]
containerize-dis (c ∨ᵈⁿᶠ d) prev = containerize-con c prev ∷⁺ containerize-dis d prev

containerize : {ℓ₁ : Level} → {n : ℕ} → {x : List (Set ℓ₁)} → {xs : Vec (List (Set ℓ₁)) n} → (C : Container ℓₛ ℓₚ) → (X : Set ℓₓ) → Formulaᵈⁿᶠ-dis (Shape C) ℓ₁ (x ∷ xs) → Previous (Shape C) ℓ₁ (x ∷ xs) → Containerⁱ C X ℓ₁ (x ∷ xs)
containerize {ℓ₁ = ℓ₁} {x = X} {xs = Xs} C α d prev with containerize-dis d prev
... | xs = containerⁱ
  where
  containerⁱ : Containerⁱ C α ℓ₁ (X ∷ Xs)
  Shapeⁱ containerⁱ = length⁺ xs
  Positionⁱ containerⁱ s i = foldr (λ (m , x) acc → position m i x ∷⁺ acc) (λ (m , x) → [ position m i x ]) (lookup' (toList xs) s)
    where
    position : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → ModalitySequence (Shape C) ℓ₁ → Program C X → Maybe' (Set ℓ₁ ⊎ FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Result C X ℓ₁
    position m i (val inj₁ x) = apply m i λ { (val _) → res (val inj₁ x) ; done → res done ; fail → res fail }
    position m i (val inj₂ x) = apply m i λ { (val o) → res (val inj₂ (o , x)) ; done → res done ; fail → res fail }
    position m i done = apply m i λ { (val _) → res done ; done → res done ; fail → res fail }
    position m i fail = apply m i λ { (val _) → res fail ; done → res done ; fail → res fail }

extend : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → (Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))) → (Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))) → Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
extend {ℓₛ = ℓₛ} {ℓₚ = ℓₚ} {ℓₓ = ℓₓ} {ℓ₁ = ℓ₁} _ _ (val inj₁ x) = Lift (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁)) x
extend mu nu (val inj₂ (x , fp , _ , _ , _ , p , prev , args)) = apply-q (proj₂ (apply-p p args)) prev x (case fp of λ { leastFP → mu ; greatestFP → nu })
  where
  apply-q : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → {n : ℕ} → {x : List (Set ℓ₁)} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Quantifiedᵈⁿᶠ (Shape C) ℓ₁ (x ∷ xs) αs → Previous (Shape C) ℓ₁ (x ∷ xs) → Program C X → (Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs)) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))) → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
  apply-q {C = C} {X = X} (formulaᵈⁿᶠ d) prev x f = ∃[ s ] ∀ {o} → let rs = Positionⁱ (containerize C X d prev) s x in unfold⁺ rs (<-wf rs) o (f o)
  apply-q (∀ᵈⁿᶠ〔 _ 〕 q) prev x f = ∀ a → apply-q (q a) prev x f
  apply-q (∃ᵈⁿᶠ〔 _ 〕 q) prev x f = ∃[ a ] apply-q (q a) prev x f

  apply-p : {S : Set ℓ} → {ℓ₁ : Level} → {n : ℕ} → {xs : Vec (List (Set ℓ₁)) n} → {αs₁ : List (Set ℓ₁)} → Parameterizedᵈⁿᶠ S ℓ₁ xs αs₁ → Arguments ℓ₁ αs₁ → ∃[ αs₂ ] Quantifiedᵈⁿᶠ S ℓ₁ xs αs₂
  apply-p (quantifiedᵈⁿᶠ_ {αs = αs} q) [] = αs , q
  apply-p (_ ↦ᵈⁿᶠ p) (a ∷ args) = apply-p (p a) args
extend _ _ done = ⊤
extend _ _ fail = ⊥

record Mu {C : Container ℓₛ ℓₚ} {X : Set ℓₓ} {ℓ₁ : Level} (_ : Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs))) : Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
record Nu {C : Container ℓₛ ℓₚ} {X : Set ℓₓ} {ℓ₁ : Level} (_ : Maybe' (Set ℓ₁ ⊎ Program C X × FixedPoint × ∃[ n ] ∃[ xs ] ∃[ αs ] (Parameterizedᵈⁿᶠ {n = suc n} (Shape C) ℓ₁ (αs ∷ xs) αs × Previous (Shape C) ℓ₁ (αs ∷ xs) × Arguments ℓ₁ αs))) : Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))

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

_⊨ᵛ_ : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → Program C X → Formulaᵈⁿᶠ-var (Shape C) ℓ₁ [] → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
_ ⊨ᵛ trueᵈⁿᶠ = ⊤
_ ⊨ᵛ falseᵈⁿᶠ = ⊥
_⊨ᵛ_ {ℓₛ = ℓₛ} {ℓₚ = ℓₚ} {ℓₓ = ℓₓ} {ℓ₁ = ℓ₁} _ (valᵈⁿᶠ x) = Lift (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁)) x
x ⊨ᵛ ⟨ af ⟩ᵈⁿᶠ v with free x
... | pure _ = ⊥
... | impure (s , c) = s ∈ af × ∃[ p ] c p ⊨ᵛ v
x ⊨ᵛ [ af ]ᵈⁿᶠ v with free x
... | pure _ = ⊤
... | impure (s , c) = s ∈ af → ∀ p → c p ⊨ᵛ v
x ⊨ᵛ μᵈⁿᶠ_．_ {αs = αs} p args = Mu (val inj₂ (x , leastFP , zero , [] , αs , p , 〔 leastFP , p 〕 , args))
x ⊨ᵛ νᵈⁿᶠ_．_ {αs = αs} p args = Nu (val inj₂ (x , greatestFP , zero , [] , αs , p , 〔 greatestFP , p 〕 , args))

infix 25 _⊨ᶜ_

_⊨ᶜ_ : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → Program C X → Formulaᵈⁿᶠ-con (Shape C) ℓ₁ [] → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
x ⊨ᶜ con-var v = x ⊨ᵛ v
x ⊨ᶜ v ∧ᵈⁿᶠ c = x ⊨ᵛ v × x ⊨ᶜ c

infix 25 _⊨ᵈ_

_⊨ᵈ_ : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → Program C X → Formulaᵈⁿᶠ-dis (Shape C) ℓ₁ [] → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
x ⊨ᵈ dis-con c = x ⊨ᶜ c
x ⊨ᵈ c ∨ᵈⁿᶠ d = x ⊨ᶜ c ⊎ x ⊨ᵈ d

data Formulaⁱ {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) : Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁))

infix 45 formula_
infix 40 ∀〔_〕_
infix 40 ∃〔_〕_

data Quantifiedⁱ {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁ ⊎ Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
  formula_ : Formulaⁱ S ℓ₁ xs → Quantifiedⁱ S ℓ₁ xs []
  ∀〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantifiedⁱ S ℓ₁ xs αs) → Quantifiedⁱ S ℓ₁ xs (inj₁ α ∷ αs)
  ∃〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantifiedⁱ S ℓ₁ xs αs) → Quantifiedⁱ S ℓ₁ xs (inj₂ α ∷ αs)

infix 35 quantified_
infix 30 _↦_

data Parameterizedⁱ {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
  quantified_ : ∀ {αs} → Quantifiedⁱ S ℓ₁ xs αs → Parameterizedⁱ S ℓ₁ xs []
  _↦_ : ∀ {αs : List (Set ℓ₁)} → (α : Set ℓ₁) → (α → Parameterizedⁱ S ℓ₁ xs αs) → Parameterizedⁱ S ℓ₁ xs (α ∷ αs)

infix 80 val_
infix 80 ref_．_
infix 75 ~_
infix 70 ⟨_⟩_
infix 70 [_]_
infixr 65 _∧_
infixr 60 _∨_
infixr 55 _⇒_
infix 50 μ_．_
infix 50 ν_．_

data Formulaⁱ S ℓ₁ where
  true false : ∀ {xs} → Formulaⁱ S ℓ₁ xs
  val_ : ∀ {xs} → Set ℓ₁ → Formulaⁱ S ℓ₁ xs
  ~_ : ∀ {xs} → Formulaⁱ S ℓ₁ xs → Formulaⁱ S ℓ₁ xs
  _∧_ _∨_ _⇒_ : ∀ {xs} → Formulaⁱ S ℓ₁ xs → Formulaⁱ S ℓ₁ xs → Formulaⁱ S ℓ₁ xs
  ⟨_⟩_ [_]_ : ∀ {xs} → RegularFormula S ℓ₁ → Formulaⁱ S ℓ₁ xs → Formulaⁱ S ℓ₁ xs
  μ_．_ ν_．_ : ∀ {αs xs} → Parameterizedⁱ S ℓ₁ (αs ∷ xs) αs → Arguments ℓ₁ αs → Formulaⁱ S ℓ₁ xs
  ref_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ₁ (lookupᵛ xs i) → Formulaⁱ S ℓ₁ xs

Formula : (S : Set ℓ) → (ℓ₁ : Level) → (αs : List (Set ℓ₁ ⊎ Set ℓ₁)) → Set (ℓ ⊔ (sucˡ ℓ₁))
Formula S ℓ₁ αs = Quantifiedⁱ S ℓ₁ [] αs

infix 25 _⊨_

_⊨_ : {C : Container ℓₛ ℓₚ} → {X : Set ℓₓ} → {ℓ₁ : Level} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Program C X → Formula (Shape C) ℓ₁ αs → Set (ℓₛ ⊔ ℓₚ ⊔ ℓₓ ⊔ (sucˡ ℓ₁))
x ⊨ ∀〔 _ 〕 qⁱ = ∀ a → x ⊨ qⁱ a
x ⊨ ∃〔 _ 〕 qⁱ = ∃[ a ] x ⊨ qⁱ a
x ⊨ formula fⁱ = x ⊨ᵈ f''→fᵈⁿᶠ (f'→f'' (fⁱ→f' fⁱ))
  where
  infix 100 actF'_
  infix 95 _*'
  infixr 90 _·'_
  infixr 85 _+'_

  data RegularFormula' (S : Set ℓ) (ℓ₁ : Level) : Set (ℓ ⊔ (sucˡ ℓ₁)) where
    ε' : RegularFormula' S ℓ₁
    actF'_ : ActionFormula S ℓ₁ → RegularFormula' S ℓ₁
    _·'_ _+'_ : RegularFormula' S ℓ₁ → RegularFormula' S ℓ₁ → RegularFormula' S ℓ₁
    _*' : RegularFormula' S ℓ₁ → RegularFormula' S ℓ₁

  rf→rf' : {S : Set ℓ} → {ℓ₁ : Level} → RegularFormula S ℓ₁ → RegularFormula' S ℓ₁
  rf→rf' ε = ε'
  rf→rf' (actF af) = actF' af
  rf→rf' (rf₁ · rf₂) = rf→rf' rf₁ ·' rf→rf' rf₂
  rf→rf' (rf₁ + rf₂) = rf→rf' rf₁ +' rf→rf' rf₂
  rf→rf' (rf *) = rf→rf' rf *'
  rf→rf' (rf ⁺) = rf' ·' (rf' *')
    where
    rf' = rf→rf' rf

  data Formula' {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) : Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁))

  infix 45 formula'_
  infix 40 ∀'〔_〕_
  infix 40 ∃'〔_〕_

  data Quantified' {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁ ⊎ Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
    formula'_ : Formula' S ℓ₁ xs → Quantified' S ℓ₁ xs []
    ∀'〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantified' S ℓ₁ xs αs) → Quantified' S ℓ₁ xs (inj₁ α ∷ αs)
    ∃'〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantified' S ℓ₁ xs αs) → Quantified' S ℓ₁ xs (inj₂ α ∷ αs)

  infix 35 quantified'_
  infix 30 _↦'_

  data Parameterized' {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
    quantified'_ : ∀ {αs} → Quantified' S ℓ₁ xs αs → Parameterized' S ℓ₁ xs []
    _↦'_ : ∀ {αs : List (Set ℓ₁)} → (α : Set ℓ₁) → (α → Parameterized' S ℓ₁ xs αs) → Parameterized' S ℓ₁ xs (α ∷ αs)

  infix 80 val'_
  infix 80 ref'_．_
  infix 75 ~'_
  infix 70 ⟨_⟩'_
  infix 70 [_]'_
  infixr 65 _∧'_
  infixr 60 _∨'_
  infixr 55 _⇒'_
  infix 50 μ'_．_
  infix 50 ν'_．_

  data Formula' S ℓ₁ where
    true' false' : ∀ {xs} → Formula' S ℓ₁ xs
    val'_ : ∀ {xs} → Set ℓ₁ → Formula' S ℓ₁ xs
    ~'_ : ∀ {xs} → Formula' S ℓ₁ xs → Formula' S ℓ₁ xs
    _∧'_ _∨'_ _⇒'_ : ∀ {xs} → Formula' S ℓ₁ xs → Formula' S ℓ₁ xs → Formula' S ℓ₁ xs
    ⟨_⟩'_ [_]'_ : ∀ {xs} → ActionFormula S ℓ₁ → Formula' S ℓ₁ xs → Formula' S ℓ₁ xs
    μ'_．_ ν'_．_ : ∀ {αs xs} → Parameterized' S ℓ₁ (αs ∷ xs) αs → Arguments ℓ₁ αs → Formula' S ℓ₁ xs
    ref'_．_ : ∀ {xs} → (i : Fin (lengthᵛ xs)) → Arguments ℓ₁ (lookupᵛ xs i) → Formula' S ℓ₁ xs

  ref⁺ : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {x : List (Set ℓ₁)} → {xs : Vec (List (Set ℓ₁)) n} → Formula' S ℓ₁ xs → Formula' S ℓ₁ (x ∷ xs)
  ref⁺ f' = ref⁺' {xs₁ = []} f'
    where
    ref⁺' : {n₁ n₂ : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {x : List (Set ℓ₁)} → {xs₁ : Vec (List (Set ℓ₁)) n₁} → {xs₂ : Vec (List (Set ℓ₁)) n₂} → Formula' S ℓ₁ (xs₁ ++ xs₂) → Formula' S ℓ₁ (xs₁ ++ x ∷ xs₂)

    ref⁺'-q : {n₁ n₂ : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {x : List (Set ℓ₁)} → {xs₁ : Vec (List (Set ℓ₁)) n₁} → {xs₂ : Vec (List (Set ℓ₁)) n₂} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Quantified' S ℓ₁ (xs₁ ++ xs₂) αs → Quantified' S ℓ₁ (xs₁ ++ x ∷ xs₂) αs
    ref⁺'-q (formula' f') = formula' ref⁺' f'
    ref⁺'-q (∀'〔 α 〕 q') = ∀'〔 α 〕 λ a → ref⁺'-q (q' a)
    ref⁺'-q (∃'〔 α 〕 q') = ∃'〔 α 〕 λ a → ref⁺'-q (q' a)

    ref⁺'-p : {n₁ n₂ : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {x : List (Set ℓ₁)} → {xs₁ : Vec (List (Set ℓ₁)) n₁} → {xs₂ : Vec (List (Set ℓ₁)) n₂} → {αs : List (Set ℓ₁)} → Parameterized' S ℓ₁ (xs₁ ++ xs₂) αs → Parameterized' S ℓ₁ (xs₁ ++ x ∷ xs₂) αs
    ref⁺'-p (quantified' q') = quantified' ref⁺'-q q'
    ref⁺'-p (α ↦' p') = α ↦' λ a → ref⁺'-p (p' a)

    ref⁺' true' = true'
    ref⁺' false' = false'
    ref⁺' (val' x) = val' x
    ref⁺' (~' f') = ~' ref⁺' f'
    ref⁺' (f'₁ ∧' f'₂) = ref⁺' f'₁ ∧' ref⁺' f'₂
    ref⁺' (f'₁ ∨' f'₂) = ref⁺' f'₁ ∨' ref⁺' f'₂
    ref⁺' (f'₁ ⇒' f'₂) = ref⁺' f'₁ ⇒' ref⁺' f'₂
    ref⁺' (⟨ af ⟩' f') = ⟨ af ⟩' ref⁺' f'
    ref⁺' ([ af ]' f') = [ af ]' ref⁺' f'
    ref⁺' {xs₁ = xs₁} (μ'_．_ {αs = αs} p' args) = μ'_．_ (ref⁺'-p {xs₁ = αs ∷ xs₁} p') args
    ref⁺' {xs₁ = xs₁} (ν'_．_ {αs = αs} p' args) = ν'_．_ (ref⁺'-p {xs₁ = αs ∷ xs₁} p') args
    ref⁺' {n₁ = n₁} {ℓ₁ = ℓ₁} {x = x} {xs₁ = xs₁} {xs₂ = xs₂} (ref' i ． args) with toℕ i <ᵇ n₁ | inspect (_<ᵇ_ (toℕ i)) n₁
    ... | false | [ hn ]⁼ = ref' i' i ． subst (Arguments ℓ₁) (hlookup x xs₁ xs₂ i (≮⇒≥ λ h → subst T hn (<⇒<ᵇ h))) args
      where
      i' : {n₁ n₂ : ℕ} → Fin (n₁ ＋ n₂) → Fin (n₁ ＋ suc n₂)
      i' {n₁ = n₁} {n₂ = n₂} i = cast (sym (+-suc n₁ n₂)) (suc i)

      hlookup : {α : Set ℓ} → {n₁ n₂ : ℕ} → (x : α) → (xs₁ : Vec α n₁) → (xs₂ : Vec α n₂) → (i : Fin (n₁ ＋ n₂)) → toℕ i ≥ n₁ → lookupᵛ (xs₁ ++ xs₂) i ≡ lookupᵛ (xs₁ ++ x ∷ xs₂) (i' i)
      hlookup _ [] _ zero _ = refl
      hlookup x [] (_ ∷ xs₂) (suc i) z≤n = hlookup x [] xs₂ i z≤n
      hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h
    ... | true | [ h ]⁼ = ref' i' i ． subst (Arguments ℓ₁) (hlookup x xs₁ xs₂ i (<ᵇ⇒< (toℕ i) n₁ (subst T (sym h) tt₀))) args
      where
      i' : {n₁ n₂ : ℕ} → Fin (n₁ ＋ n₂) → Fin (n₁ ＋ suc n₂)
      i' {n₁ = n₁} {n₂ = n₂} i = cast (sym (+-suc n₁ n₂)) (inject₁ i)

      hlookup : {α : Set ℓ} → {n₁ n₂ : ℕ} → (x : α) → (xs₁ : Vec α n₁) → (xs₂ : Vec α n₂) → (i : Fin (n₁ ＋ n₂)) → toℕ i <ⁿ n₁ → lookupᵛ (xs₁ ++ xs₂) i ≡ lookupᵛ (xs₁ ++ x ∷ xs₂) (i' i)
      hlookup _ (_ ∷ _) _ zero _ = refl
      hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h

  fⁱ→f' : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formulaⁱ S ℓ₁ xs → Formula' S ℓ₁ xs

  qⁱ→q' : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Quantifiedⁱ S ℓ₁ xs αs → Quantified' S ℓ₁ xs αs
  qⁱ→q' (formula fⁱ) = formula' fⁱ→f' fⁱ
  qⁱ→q' (∀〔 α 〕 qⁱ) = ∀'〔 α 〕 λ a → qⁱ→q' (qⁱ a)
  qⁱ→q' (∃〔 α 〕 qⁱ) = ∃'〔 α 〕 λ a → qⁱ→q' (qⁱ a)

  pⁱ→p' : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁)} → Parameterizedⁱ S ℓ₁ xs αs → Parameterized' S ℓ₁ xs αs
  pⁱ→p' (quantified qⁱ) = quantified' qⁱ→q' qⁱ
  pⁱ→p' (α ↦ pⁱ) = α ↦' λ a → pⁱ→p' (pⁱ a)

  fⁱ→f' true = true'
  fⁱ→f' false = false'
  fⁱ→f' (val x) = val' x
  fⁱ→f' (~ fⁱ) = ~' fⁱ→f' fⁱ
  fⁱ→f' (fⁱ₁ ∧ fⁱ₂) = fⁱ→f' fⁱ₁ ∧' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ∨ fⁱ₂) = fⁱ→f' fⁱ₁ ∨' fⁱ→f' fⁱ₂
  fⁱ→f' (fⁱ₁ ⇒ fⁱ₂) = fⁱ→f' fⁱ₁ ⇒' fⁱ→f' fⁱ₂
  fⁱ→f' (⟨ rf ⟩ fⁱ) = helper-∃ (rf→rf' rf) (fⁱ→f' fⁱ)
    where
    helper-∃ : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → RegularFormula' S ℓ₁ → Formula' S ℓ₁ xs → Formula' S ℓ₁ xs
    helper-∃ ε' f' = f'
    helper-∃ (actF' af) f' = ⟨ af ⟩' f'
    helper-∃ (rf'₁ ·' rf'₂) f' = helper-∃ rf'₁ (helper-∃ rf'₂ f')
    helper-∃ (rf'₁ +' rf'₂) f' = helper-∃ rf'₁ f' ∨' helper-∃ rf'₂ f'
    helper-∃ (rf' *') f' = μ' quantified' (formula' (helper-∃ rf' (ref' zero ． []) ∨' ref⁺ f')) ． []
  fⁱ→f' ([ rf ] fⁱ) = helper-∀ (rf→rf' rf) (fⁱ→f' fⁱ)
    where
    helper-∀ : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → RegularFormula' S ℓ₁ → Formula' S ℓ₁ xs → Formula' S ℓ₁ xs
    helper-∀ ε' f' = f'
    helper-∀ (actF' af) f' = [ af ]' f'
    helper-∀ (rf'₁ ·' rf'₂) f' = helper-∀ rf'₁ (helper-∀ rf'₂ f')
    helper-∀ (rf'₁ +' rf'₂) f' = helper-∀ rf'₁ f' ∨' helper-∀ rf'₂ f'
    helper-∀ (rf' *') f' = ν' quantified' (formula' (helper-∀ rf' (ref' zero ． []) ∨' ref⁺ f')) ． []
  fⁱ→f' (μ pⁱ ． args) = μ' pⁱ→p' pⁱ ． args
  fⁱ→f' (ν pⁱ ． args) = ν' pⁱ→p' pⁱ ． args
  fⁱ→f' (ref i ． args) = ref' i ． args

  data Formula'' {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) : Vec (List (Set ℓ₁)) n → Set (ℓ ⊔ (sucˡ ℓ₁))

  infix 45 formula''_
  infix 40 ∀''〔_〕_
  infix 40 ∃''〔_〕_

  data Quantified'' {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁ ⊎ Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
    formula''_ : Formula'' S ℓ₁ xs → Quantified'' S ℓ₁ xs []
    ∀''〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantified'' S ℓ₁ xs αs) → Quantified'' S ℓ₁ xs (inj₁ α ∷ αs)
    ∃''〔_〕_ : ∀ {αs} → (α : Set ℓ₁) → (α → Quantified'' S ℓ₁ xs αs) → Quantified'' S ℓ₁ xs (inj₂ α ∷ αs)

  infix 35 quantified''_
  infix 30 _↦''_

  data Parameterized'' {n : ℕ} (S : Set ℓ) (ℓ₁ : Level) (xs : Vec (List (Set ℓ₁)) n) : List (Set ℓ₁) → Set (ℓ ⊔ (sucˡ ℓ₁)) where
    quantified''_ : ∀ {αs} → Quantified'' S ℓ₁ xs αs → Parameterized'' S ℓ₁ xs []
    _↦''_ : ∀ {αs : List (Set ℓ₁)} → (α : Set ℓ₁) → (α → Parameterized'' S ℓ₁ xs αs) → Parameterized'' S ℓ₁ xs (α ∷ αs)

  infix 80 val''_
  infix 80 ref''〔_〕_．_
  infix 70 ⟨_⟩''_
  infix 70 [_]''_
  infixr 65 _∧''_
  infixr 60 _∨''_
  infix 50 μ''_．_
  infix 50 ν''_．_

  data Formula'' S ℓ₁ where
    true'' false'' : ∀ {xs} → Formula'' S ℓ₁ xs
    val''_ : ∀ {xs} → Set ℓ₁ → Formula'' S ℓ₁ xs
    _∧''_ _∨''_ : ∀ {xs} → Formula'' S ℓ₁ xs → Formula'' S ℓ₁ xs → Formula'' S ℓ₁ xs
    ⟨_⟩''_ [_]''_ : ∀ {xs} → ActionFormula S ℓ₁ → Formula'' S ℓ₁ xs → Formula'' S ℓ₁ xs
    μ''_．_ ν''_．_ : ∀ {αs xs} → Parameterized'' S ℓ₁ (αs ∷ xs) αs → Arguments ℓ₁ αs → Formula'' S ℓ₁ xs
    ref''〔_〕_．_ : ∀ {xs} → Bool → (i : Fin (lengthᵛ xs)) → Arguments ℓ₁ (lookupᵛ xs i) → Formula'' S ℓ₁ xs

  flipRef : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Fin n → Formula'' S ℓ₁ xs → Formula'' S ℓ₁ xs

  flipRef-q : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Fin n → Quantified'' S ℓ₁ xs αs → Quantified'' S ℓ₁ xs αs
  flipRef-q x (formula'' f'') = formula'' flipRef x f''
  flipRef-q x (∀''〔 α 〕 q'') = ∀''〔 α 〕 λ a → flipRef-q x (q'' a)
  flipRef-q x (∃''〔 α 〕 q'') = ∃''〔 α 〕 λ a → flipRef-q x (q'' a)

  flipRef-p : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁)} → Fin n → Parameterized'' S ℓ₁ xs αs → Parameterized'' S ℓ₁ xs αs
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

  negate : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formula'' S ℓ₁ xs → Formula'' S ℓ₁ xs

  negate-q : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Quantified'' S ℓ₁ xs αs → Quantified'' S ℓ₁ xs αs
  negate-q (formula'' f'') = formula'' negate f''
  negate-q (∀''〔 α 〕 q'') = ∀''〔 α 〕 λ a → negate-q (q'' a)
  negate-q (∃''〔 α 〕 q'') = ∃''〔 α 〕 λ a → negate-q (q'' a)

  negate-p : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁)} → Parameterized'' S ℓ₁ xs αs → Parameterized'' S ℓ₁ xs αs
  negate-p (quantified'' q'') = quantified'' negate-q q''
  negate-p (α ↦'' p'') = α ↦'' λ a → negate-p (p'' a)

  negate true'' = false''
  negate false'' = true''
  negate (val'' x) = val'' (¬ x)
  negate (f''₁ ∧'' f''₂) = negate f''₁ ∨'' negate f''₂
  negate (f''₁ ∨'' f''₂) = negate f''₁ ∧'' negate f''₂
  negate (⟨ af ⟩'' f'') = [ af ]'' negate f''
  negate ([ af ]'' f'') = ⟨ af ⟩'' negate f''
  negate (μ'' p'' ． args) = ν'' flipRef-p zero (negate-p p'') ． args
  negate (ν'' p'' ． args) = μ'' flipRef-p zero (negate-p p'') ． args
  negate (ref''〔 b 〕 i ． args) = ref''〔 not b 〕 i ． args

  f'→f'' : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formula' S ℓ₁ xs → Formula'' S ℓ₁ xs

  q'→q'' : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Quantified' S ℓ₁ xs αs → Quantified'' S ℓ₁ xs αs
  q'→q'' (formula' f') = formula'' f'→f'' f'
  q'→q'' (∀'〔 α 〕 q') = ∀''〔 α 〕 λ a → q'→q'' (q' a)
  q'→q'' (∃'〔 α 〕 q') = ∃''〔 α 〕 λ a → q'→q'' (q' a)

  p'→p'' : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁)} → Parameterized' S ℓ₁ xs αs → Parameterized'' S ℓ₁ xs αs
  p'→p'' (quantified' q') = quantified'' q'→q'' q'
  p'→p'' (α ↦' p') = α ↦'' λ a → p'→p'' (p' a)

  f'→f'' true' = true''
  f'→f'' false' = false''
  f'→f'' (val' x) = val'' x
  f'→f'' (~' f') = negate (f'→f'' f')
  f'→f'' (f'₁ ∧' f'₂) = f'→f'' f'₁ ∧'' f'→f'' f'₂
  f'→f'' (f'₁ ∨' f'₂) = f'→f'' f'₁ ∨'' f'→f'' f'₂
  f'→f'' (f'₁ ⇒' f'₂) = negate (f'→f'' f'₁) ∨'' f'→f'' f'₂
  f'→f'' (⟨ af ⟩' f') = ⟨ af ⟩'' f'→f'' f'
  f'→f'' ([ af ]' f') = [ af ]'' f'→f'' f'
  f'→f'' (μ' p' ． args) = μ'' p'→p'' p' ． args
  f'→f'' (ν' p' ． args) = ν'' p'→p'' p' ． args
  f'→f'' (ref' i ． args) = ref''〔 true 〕 i ． args

  merge-dis-dis-or : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs
  merge-dis-dis-or (dis-con c) d = c ∨ᵈⁿᶠ d
  merge-dis-dis-or (c ∨ᵈⁿᶠ d₁) d₂ = c ∨ᵈⁿᶠ merge-dis-dis-or d₁ d₂

  merge-con-con : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs
  merge-con-con (con-var v) c = v ∧ᵈⁿᶠ c
  merge-con-con (v ∧ᵈⁿᶠ c₁) c₂ = v ∧ᵈⁿᶠ merge-con-con c₁ c₂

  merge-con-dis : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs
  merge-con-dis c₁ (dis-con c₂) = dis-con (merge-con-con c₁ c₂)
  merge-con-dis c₁ (c₂ ∨ᵈⁿᶠ d₂) = merge-con-con c₁ c₂ ∨ᵈⁿᶠ merge-con-dis c₁ d₂

  merge-dis-dis-and : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs
  merge-dis-dis-and (dis-con c) d = merge-con-dis c d
  merge-dis-dis-and (c ∨ᵈⁿᶠ d₁) d₂ = merge-dis-dis-or (merge-con-dis c d₂) (merge-dis-dis-and d₁ d₂)

  f''→fᵈⁿᶠ : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → Formula'' S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs

  q''→qᵈⁿᶠ : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁ ⊎ Set ℓ₁)} → Quantified'' S ℓ₁ xs αs → Quantifiedᵈⁿᶠ S ℓ₁ xs αs
  q''→qᵈⁿᶠ (formula'' f'') = formulaᵈⁿᶠ f''→fᵈⁿᶠ f''
  q''→qᵈⁿᶠ (∀''〔 α 〕 q'') = ∀ᵈⁿᶠ〔 α 〕 λ a → q''→qᵈⁿᶠ (q'' a)
  q''→qᵈⁿᶠ (∃''〔 α 〕 q'') = ∃ᵈⁿᶠ〔 α 〕 λ a → q''→qᵈⁿᶠ (q'' a)

  p''→pᵈⁿᶠ : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → {αs : List (Set ℓ₁)} → Parameterized'' S ℓ₁ xs αs → Parameterizedᵈⁿᶠ S ℓ₁ xs αs
  p''→pᵈⁿᶠ (quantified'' q'') = quantifiedᵈⁿᶠ q''→qᵈⁿᶠ q''
  p''→pᵈⁿᶠ (α ↦'' p'') = α ↦ᵈⁿᶠ λ a → p''→pᵈⁿᶠ (p'' a)

  f''→fᵈⁿᶠ true'' = dis-con con-var trueᵈⁿᶠ
  f''→fᵈⁿᶠ false'' = dis-con con-var falseᵈⁿᶠ
  f''→fᵈⁿᶠ (val'' x) = dis-con con-var valᵈⁿᶠ x
  f''→fᵈⁿᶠ (f''₁ ∧'' f''₂) = merge-dis-dis-and (f''→fᵈⁿᶠ f''₁) (f''→fᵈⁿᶠ f''₂)
  f''→fᵈⁿᶠ (f''₁ ∨'' f''₂) = merge-dis-dis-or (f''→fᵈⁿᶠ f''₁) (f''→fᵈⁿᶠ f''₂)
  f''→fᵈⁿᶠ (⟨ af ⟩'' f'') = merge-∃-dis af (f''→fᵈⁿᶠ f'')
    where
    merge-∃-var : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-var S ℓ₁ xs → Formulaᵈⁿᶠ-var S ℓ₁ xs
    merge-∃-var af v = ⟨ af ⟩ᵈⁿᶠ v

    merge-∃-con : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs
    merge-∃-con af (con-var v) = con-var (merge-∃-var af v)
    merge-∃-con af (v ∧ᵈⁿᶠ c) = merge-∃-var af v ∧ᵈⁿᶠ merge-∃-con af c

    merge-∃-dis : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs
    merge-∃-dis af (dis-con c) = dis-con (merge-∃-con af c)
    merge-∃-dis af (c ∨ᵈⁿᶠ d) = merge-∃-con af c ∨ᵈⁿᶠ merge-∃-dis af d
  f''→fᵈⁿᶠ ([ af ]'' f'') = merge-∀-dis af (f''→fᵈⁿᶠ f'')
    where
    merge-∀-var : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-var S ℓ₁ xs → Formulaᵈⁿᶠ-var S ℓ₁ xs
    merge-∀-var af v = [ af ]ᵈⁿᶠ v

    merge-∀-con : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-con S ℓ₁ xs → Formulaᵈⁿᶠ-con S ℓ₁ xs
    merge-∀-con af (con-var v) = con-var (merge-∀-var af v)
    merge-∀-con af (v ∧ᵈⁿᶠ c) = merge-∀-var af v ∧ᵈⁿᶠ merge-∀-con af c

    merge-∀-dis : {n : ℕ} → {S : Set ℓ} → {ℓ₁ : Level} → {xs : Vec (List (Set ℓ₁)) n} → ActionFormula S ℓ₁ → Formulaᵈⁿᶠ-dis S ℓ₁ xs → Formulaᵈⁿᶠ-dis S ℓ₁ xs
    merge-∀-dis af (dis-con c) = dis-con (merge-∀-con af c)
    merge-∀-dis af (c ∨ᵈⁿᶠ d) = merge-∀-con af c ∨ᵈⁿᶠ merge-∀-dis af d
  f''→fᵈⁿᶠ (μ'' p'' ． args) = dis-con con-var μᵈⁿᶠ p''→pᵈⁿᶠ p'' ． args
  f''→fᵈⁿᶠ (ν'' p'' ． args) = dis-con con-var νᵈⁿᶠ p''→pᵈⁿᶠ p'' ． args
  f''→fᵈⁿᶠ (ref''〔 false 〕 i ． args) = dis-con con-var falseᵈⁿᶠ
  f''→fᵈⁿᶠ (ref''〔 true 〕 i ． args) = dis-con con-var refᵈⁿᶠ i ． args
