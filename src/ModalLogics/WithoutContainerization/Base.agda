{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerization.Base where

open import Common.Program using (pure; impure; Program; free)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula; _∈_)
open import Data.Bool using (Bool; not; T)
open import Data.Container using (Container; Shape)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; toℕ; cast; inject₁)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc; z≤n; s≤s; _≥_; _<_; _<ᵇ_) renaming (_+_ to _＋_)
open import Data.Nat.Properties using (+-suc; ≮⇒≥; <⇒<ᵇ; <ᵇ⇒<)
open import Data.Product using (_,_; _×_; map₁; map₂; proj₂; ∃-syntax; Σ-syntax)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; length; map; _++_) renaming (lookup to lookupᵛ)
open import Function using (case_of_; _∘_)
open import Level using (Lift; Level; _⊔_) renaming (suc to sucˡ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; inspect; sym) renaming ([_] to [_]⁼)
open import Relation.Nullary using (no; yes; ¬_)

open RegularFormula
open Bool
open Fin
open List
open Maybe
open Vec
open _≡_

private variable
  s ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {α αs} → α → Arguments ℓ αs → Arguments ℓ (α ∷ αs)

module Aux where

  data ActionTree (S : Set s) (ℓ : Level) : Set (s ⊔ sucˡ ℓ)

  data ActionNode (S : Set s) (ℓ : Level) : Set (s ⊔ sucˡ ℓ) where
    ε : ActionNode S ℓ
    actF_ : ActionFormula S ℓ → ActionNode S ℓ
    _* : ActionTree S ℓ → ActionNode S ℓ

  data ActionTree S ℓ where
    ⦗_⦘ : ActionNode S ℓ → ActionTree S ℓ
    _·_ : ActionNode S ℓ → ActionTree S ℓ → ActionTree S ℓ
    _+_ : ActionTree S ℓ → ActionTree S ℓ → ActionTree S ℓ

  concatenate : {S : Set s} → {ℓ : Level} → ActionTree S ℓ → ActionTree S ℓ → ActionTree S ℓ
  concatenate ⦗ x ⦘ at₂ = x · at₂
  concatenate (x · at₁) at₂ = x · concatenate at₁ at₂
  concatenate (at₁ + at₂) at₃ = concatenate at₁ at₃ + concatenate at₂ at₃

  desugar-rf : {S : Set s} → {ℓ : Level} → RegularFormula S ℓ → ActionTree S ℓ
  desugar-rf ε = ⦗ ε ⦘
  desugar-rf (actF af) = ⦗ actF af ⦘
  desugar-rf (rf₁ · rf₂) = concatenate (desugar-rf rf₁) (desugar-rf rf₂)
  desugar-rf (rf₁ + rf₂) = desugar-rf rf₁ + desugar-rf rf₂
  desugar-rf (rf *) = ⦗ desugar-rf rf * ⦘
  desugar-rf (rf ⁺) = let at = desugar-rf rf in concatenate at ⦗ at * ⦘

  infix 60 val_
  infix 60 ref_⦗_⦘
  infix 50 ⟨_⟩_
  infix 50 [_]_
  infixr 45 _∧_
  infixr 40 _∨_
  infix 30 ∀⦗_⦘_
  infix 30 ∃⦗_⦘_
  infix 30 μ_
  infix 30 ν_

  data Formula' {n : ℕ} (S : Set s) (ℓ : Level) : Vec (List (Set ℓ)) n → Set (s ⊔ sucˡ ℓ)

  infix 70 formula_
  infix 65 _＝_↦_

  data Parameterized' {n : ℕ} (S : Set s) (ℓ : Level) (xs : Vec (List (Set ℓ)) n) : List (Set ℓ) → Set (s ⊔ (sucˡ ℓ)) where
    formula_ : Formula' S ℓ xs → Parameterized' S ℓ xs []
    _＝_↦_ : ∀ {αs} → (α : Set ℓ) → α → (α → Parameterized' S ℓ xs αs) → Parameterized' S ℓ xs (α ∷ αs)

  data Formula' S ℓ where
    true false : ∀ {xs} → Formula' S ℓ xs
    val_ : ∀ {xs} → Set ℓ → Formula' S ℓ xs
    _∧_ _∨_ : ∀ {xs} → Formula' S ℓ xs → Formula' S ℓ xs → Formula' S ℓ xs
    ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {xs} → (α : Set ℓ) → (α → Formula' S ℓ xs) → Formula' S ℓ xs
    ⟨_⟩_ [_]_ : ∀ {xs} → ActionTree S ℓ → Formula' S ℓ xs → Formula' S ℓ xs
    μ_ ν_ : ∀ {αs xs} → Parameterized' S ℓ (αs ∷ xs) αs → Formula' S ℓ xs
    ref_⦗_⦘ : ∀ {xs} → (i : Fin (length xs)) → Arguments ℓ (lookupᵛ xs i) → Formula' S ℓ xs

  applyᵈ : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterized' S ℓ xs αs → Formula' S ℓ xs
  applyᵈ (formula f') = f'
  applyᵈ (_ ＝ a ↦ p') = applyᵈ (p' a)

  apply : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterized' S ℓ xs αs → Arguments ℓ αs → Formula' S ℓ xs
  apply (formula f') _ = f'
  apply (_ ＝ _ ↦ p') (a ∷ args) = apply (p' a) args

  data Previous (S : Set s) (ℓ : Level) : {n : ℕ} → Vec (List (Set ℓ)) n → Set (s ⊔ (sucˡ ℓ)) where
    [] : Previous S ℓ []
    _∷_ : ∀ {αs : List (Set ℓ)} {n : ℕ} {xs : Vec (List (Set ℓ)) n} → Bool × Parameterized' S ℓ (αs ∷ xs) αs → Previous S ℓ xs → Previous S ℓ (αs ∷ xs)

  lookup : {n₁ : ℕ} → {S : Set s} → {ℓ : Level} → {xs₁ : Vec (List (Set ℓ)) n₁} → Previous S ℓ xs₁ → (i : Fin n₁) → let αs = lookupᵛ xs₁ i in Bool × ∃[ n₂ ] Σ[ xs₂ ∈ Vec (List (Set ℓ)) n₂ ] Parameterized' S ℓ (αs ∷ xs₂) αs × Previous S ℓ (αs ∷ xs₂)
  lookup {n₁ = suc n} {xs₁ = _ ∷ xs} prev@((fp , p') ∷ _) zero = fp , n , xs , p' , prev
  lookup (_ ∷ prev) (suc i) = lookup prev i

  ref⁺ : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (List (Set ℓ)) n} → {x : List (Set ℓ)} → Formula' S ℓ xs → Formula' S ℓ (x ∷ xs)
  ref⁺ f' = ref⁺' {xs₁ = []} f'
    where
    ref⁺' : {n₁ n₂ : ℕ} → {S : Set s} → {ℓ : Level} → {xs₁ : Vec (List (Set ℓ)) n₁} → {xs₂ : Vec (List (Set ℓ)) n₂} → {x : List (Set ℓ)} → Formula' S ℓ (xs₁ ++ xs₂) → Formula' S ℓ (xs₁ ++ x ∷ xs₂)

    ref⁺'-p : {n₁ n₂ : ℕ} → {S : Set s} → {ℓ : Level} → {xs₁ : Vec (List (Set ℓ)) n₁} → {xs₂ : Vec (List (Set ℓ)) n₂} → {αs : List (Set ℓ)} → {x : List (Set ℓ)} → Parameterized' S ℓ (xs₁ ++ xs₂) αs → Parameterized' S ℓ (xs₁ ++ x ∷ xs₂) αs
    ref⁺'-p (formula f') = formula ref⁺' f'
    ref⁺'-p (α ＝ a ↦ p') = α ＝ a ↦ (ref⁺'-p ∘ p')

    ref⁺' true = true
    ref⁺' false = false
    ref⁺' (val x) = val x
    ref⁺' (f'₁ ∧ f'₂) = ref⁺' f'₁ ∧ ref⁺' f'₂
    ref⁺' (f'₁ ∨ f'₂) = ref⁺' f'₁ ∨ ref⁺' f'₂
    ref⁺' (∀⦗ α ⦘ f') = ∀⦗ α ⦘ (ref⁺' ∘ f')
    ref⁺' (∃⦗ α ⦘ f') = ∃⦗ α ⦘ (ref⁺' ∘ f')
    ref⁺' (⟨ af ⟩ f') = ⟨ af ⟩ ref⁺' f'
    ref⁺' ([ af ] f') = [ af ] ref⁺' f'
    ref⁺' {xs₁ = xs₁} (μ_ {αs = αs} p') = μ_ (ref⁺'-p {xs₁ = αs ∷ xs₁} p')
    ref⁺' {xs₁ = xs₁} (ν_ {αs = αs} p') = ν_ (ref⁺'-p {xs₁ = αs ∷ xs₁} p')
    ref⁺' {n₁ = n₁} {ℓ = ℓ} {xs₁ = xs₁} {xs₂ = xs₂} {x = x} (ref i ⦗ args ⦘) with toℕ i <ᵇ n₁ | inspect (_<ᵇ_ (toℕ i)) n₁
    ... | false | [ hn ]⁼ = ref i' i ⦗ subst (Arguments ℓ) (hlookup x xs₁ xs₂ i (≮⇒≥ λ h → subst T hn (<⇒<ᵇ h))) args ⦘
      where
      i' : {n₁ n₂ : ℕ} → Fin (n₁ ＋ n₂) → Fin (n₁ ＋ suc n₂)
      i' {n₁ = n₁} {n₂ = n₂} i = cast (sym (+-suc n₁ n₂)) (suc i)

      hlookup : {ℓ : Level} → {α : Set ℓ} → {n₁ n₂ : ℕ} → (x : α) → (xs₁ : Vec α n₁) → (xs₂ : Vec α n₂) → (i : Fin (n₁ ＋ n₂)) → toℕ i ≥ n₁ → lookupᵛ (xs₁ ++ xs₂) i ≡ lookupᵛ (xs₁ ++ x ∷ xs₂) (i' i)
      hlookup _ [] _ zero _ = refl
      hlookup x [] (_ ∷ xs₂) (suc i) z≤n = hlookup x [] xs₂ i z≤n
      hlookup {ℓ = ℓ} x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h
    ... | true | [ h ]⁼ = ref i' i ⦗ subst (Arguments ℓ) (hlookup x xs₁ xs₂ i (<ᵇ⇒< (toℕ i) n₁ (subst T (sym h) tt₀))) args ⦘
      where
      i' : {n₁ n₂ : ℕ} → Fin (n₁ ＋ n₂) → Fin (n₁ ＋ suc n₂)
      i' {n₁ = n₁} {n₂ = n₂} i = cast (sym (+-suc n₁ n₂)) (inject₁ i)

      hlookup : {ℓ : Level} → {α : Set ℓ} → {n₁ n₂ : ℕ} → (x : α) → (xs₁ : Vec α n₁) → (xs₂ : Vec α n₂) → (i : Fin (n₁ ＋ n₂)) → toℕ i < n₁ → lookupᵛ (xs₁ ++ xs₂) i ≡ lookupᵛ (xs₁ ++ x ∷ xs₂) (i' i)
      hlookup _ (_ ∷ _) _ zero _ = refl
      hlookup x (_ ∷ xs₁) xs₂ (suc i) (s≤s h) = hlookup x xs₁ xs₂ i h

  infix 25 _⊨'_⦗_⦘

  _⊨'_⦗_⦘ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {ℓ : Level} → {n : ℕ} → {xs : Vec (List (Set ℓ)) n} → Program C α → Formula' (Shape C) ℓ xs → Previous (Shape C) ℓ xs → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)

  record Mu {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} {ℓ : Level} {n : ℕ} {xs : Vec (List (Set ℓ)) n} (x : Program C α) (f : Formula' (Shape C) ℓ xs) (prev : Previous (Shape C) ℓ xs) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    inductive
    constructor muᶜ
    field
      mu : x ⊨' f ⦗ prev ⦘

  record Nu {C : Container ℓ₁ ℓ₂} {α : Set ℓ₃} {ℓ : Level} {n : ℕ} {xs : Vec (List (Set ℓ)) n} (x : Program C α) (f : Formula' (Shape C) ℓ xs) (prev : Previous (Shape C) ℓ xs) : Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    constructor nuᶜ
    field
      nu : x ⊨' f ⦗ prev ⦘

  _ ⊨' true ⦗ _ ⦘ = ⊤
  _ ⊨' false ⦗ _ ⦘ = ⊥
  _⊨'_⦗_⦘ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {ℓ = ℓ} _ (val x) _ = Lift (ℓ ⊔ ℓ₁ ⊔ ℓ₂) x
  x ⊨' f'₁ ∧ f'₂ ⦗ prev ⦘ = x ⊨' f'₁ ⦗ prev ⦘ × x ⊨' f'₂ ⦗ prev ⦘
  x ⊨' f'₁ ∨ f'₂ ⦗ prev ⦘ = x ⊨' f'₁ ⦗ prev ⦘ ⊎ x ⊨' f'₂ ⦗ prev ⦘
  x ⊨' ∀⦗ _ ⦘ f' ⦗ prev ⦘ = ∀ a → x ⊨' f' a ⦗ prev ⦘
  x ⊨' ∃⦗ _ ⦘ f' ⦗ prev ⦘ = ∃[ a ] x ⊨' f' a ⦗ prev ⦘
  x ⊨' ⟨ at ⟩ f' ⦗ prev ⦘ = x ⊨'⟪ at ⟫ f' ⦗ prev ⦘
    where
    _⊨'⟪_⟫_⦗_⦘ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {ℓ : Level} → {n : ℕ} → {xs : Vec (List (Set ℓ)) n} → Program C α → ActionTree (Shape C) ℓ → Formula' (Shape C) ℓ xs → Previous (Shape C) ℓ xs → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    x ⊨'⟪ ⦗ ε ⦘ ⟫ f' ⦗ prev ⦘ = x ⊨' f' ⦗ prev ⦘
    x ⊨'⟪ ⦗ actF af ⦘ ⟫ f' ⦗ prev ⦘ with free x
    ... | pure _ = ⊥
    ... | impure (s , c) = s ∈ af × ∃[ r ] c r ⊨' f' ⦗ prev ⦘
    x ⊨'⟪ ⦗ at * ⦘ ⟫ f' ⦗ prev ⦘ = let f = ⟨ at ⟩ ref zero ⦗ [] ⦘ ∨ ref⁺ f' in Mu x f ((false , formula f) ∷ prev)
    x ⊨'⟪ ε · at ⟫ f' ⦗ prev ⦘ = x ⊨'⟪ at ⟫ f' ⦗ prev ⦘
    x ⊨'⟪ (actF af) · at ⟫ f' ⦗ prev ⦘ with free x
    ... | pure _ = ⊥
    ... | impure (s , c) = s ∈ af × ∃[ r ] c r ⊨'⟪ at ⟫ f' ⦗ prev ⦘
    x ⊨'⟪ (at₁ *) · at₂ ⟫ f' ⦗ prev ⦘ = let f = ⟨ at₁ ⟩ ref zero ⦗ [] ⦘ ∨ ⟨ at₂ ⟩ (ref⁺ f') in Mu x f ((false , formula f) ∷ prev)
    x ⊨'⟪ at₁ + at₂ ⟫ f' ⦗ prev ⦘ = x ⊨'⟪ at₁ ⟫ f' ⦗ prev ⦘ ⊎ x ⊨'⟪ at₂ ⟫ f' ⦗ prev ⦘
  x ⊨' [ at ] f' ⦗ prev ⦘ = x ⊨'⟦ at ⟧ f' ⦗ prev ⦘
    where
    _⊨'⟦_⟧_⦗_⦘ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {ℓ : Level} → {n : ℕ} → {xs : Vec (List (Set ℓ)) n} → Program C α → ActionTree (Shape C) ℓ → Formula' (Shape C) ℓ xs → Previous (Shape C) ℓ xs → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    x ⊨'⟦ ⦗ ε ⦘ ⟧ f' ⦗ prev ⦘ = x ⊨' f' ⦗ prev ⦘
    x ⊨'⟦ ⦗ actF af ⦘ ⟧ f' ⦗ prev ⦘ with free x
    ... | pure _ = ⊤
    ... | impure (s , c) = s ∈ af → ∀ r → c r ⊨' f' ⦗ prev ⦘
    x ⊨'⟦ ⦗ at * ⦘ ⟧ f' ⦗ prev ⦘ = let f = [ at ] ref zero ⦗ [] ⦘ ∧ ref⁺ f' in Nu x f ((true , formula f) ∷ prev)
    x ⊨'⟦ ε · at ⟧ f' ⦗ prev ⦘ = x ⊨'⟦ at ⟧ f' ⦗ prev ⦘
    x ⊨'⟦ (actF af) · at ⟧ f' ⦗ prev ⦘  with free x
    ... | pure _ = ⊤
    ... | impure (s , c) = s ∈ af → ∀ r → c r ⊨'⟦ at ⟧ f' ⦗ prev ⦘
    x ⊨'⟦ (at₁ *) · at₂ ⟧ f' ⦗ prev ⦘ = let f = [ at₁ ] ref zero ⦗ [] ⦘ ∧ [ at₂ ] (ref⁺ f') in Nu x f ((true , formula f) ∷ prev)
    x ⊨'⟦ at₁ + at₂ ⟧ f' ⦗ prev ⦘ = x ⊨'⟦ at₁ ⟧ f' ⦗ prev ⦘ × x ⊨'⟦ at₂ ⟧ f' ⦗ prev ⦘
  x ⊨' μ p' ⦗ prev ⦘ = Mu x (applyᵈ p') ((false , p') ∷ prev)
  x ⊨' ν p' ⦗ prev ⦘ = Nu x (applyᵈ p') ((true , p') ∷ prev)
  x ⊨' ref i ⦗ args ⦘ ⦗ prev ⦘ with lookup prev i
  ... | false , _ , _ , p' , prev = Mu x (apply p' args) prev
  ... | true , _ , _ , p' , prev = Nu x (apply p' args) prev

  find : {α : Set ℓ₁} → {β : Set ℓ₂} → {n : ℕ} → Vec (α × β) n → α → DecidableEquality α → Maybe (Fin n × β)
  find [] _ _ = nothing
  find ((a₁ , b) ∷ xs) a₂ _≟_ with a₁ ≟ a₂
  ... | yes _ = just (zero , b)
  ... | no _ with find xs a₂ _≟_
  ...   | just (i , b) = just (suc i , b)
  ...   | nothing = nothing

open Aux using (Formula'; Parameterized'; []; desugar-rf; _⊨'_⦗_⦘; find)
open Aux using (Mu; Nu; muᶜ; nuᶜ) public

open Formula'
open Parameterized'

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

data Formulaⁱ {n : ℕ} (S : Set s) (ℓ : Level) : Vec (String × Bool × List (Set ℓ)) n → Set (s ⊔ sucˡ ℓ)

infix 70 formula_
infix 65 _＝_↦_

data Parameterizedⁱ {n : ℕ} (S : Set s) (ℓ : Level) (xs : Vec (String × Bool × List (Set ℓ)) n) : List (Set ℓ) → Set (s ⊔ (sucˡ ℓ)) where
  formula_ : Formulaⁱ S ℓ xs → Parameterizedⁱ S ℓ xs []
  _＝_↦_ : ∀ {αs} → (α : Set ℓ) → α → (α → Parameterizedⁱ S ℓ xs αs) → Parameterizedⁱ S ℓ xs (α ∷ αs)

data Formulaⁱ S ℓ where
  true false : ∀ {xs} → Formulaⁱ S ℓ xs
  val_ : ∀ {xs} → Set ℓ → Formulaⁱ S ℓ xs
  ~_ : ∀ {xs} → Formulaⁱ S ℓ (map (map₂ (map₁ not)) xs) → Formulaⁱ S ℓ xs
  _∧_ _∨_ : ∀ {xs} → Formulaⁱ S ℓ xs → Formulaⁱ S ℓ xs → Formulaⁱ S ℓ xs
  _⇒_ : ∀ {xs} → Formulaⁱ S ℓ (map (map₂ (map₁ not)) xs) → Formulaⁱ S ℓ xs → Formulaⁱ S ℓ xs
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {xs} → (α : Set ℓ) → (α → Formulaⁱ S ℓ xs) → Formulaⁱ S ℓ xs
  ⟨_⟩_ [_]_ : ∀ {xs} → RegularFormula S ℓ → Formulaⁱ S ℓ xs → Formulaⁱ S ℓ xs
  μ_．_ ν_．_ : ∀ {αs xs} → (name : String) → Parameterizedⁱ S ℓ ((name , true , αs) ∷ xs) αs → Formulaⁱ S ℓ xs
  ref_⦗_⦘ : ∀ {xs} → (name : String) → case find xs name _≟_ of (λ { (just (_ , true , αs)) → Arguments ℓ αs
                                                                   ; _ → ⊥ }) → Formulaⁱ S ℓ xs

Formula : (S : Set s) → (ℓ : Level) → Set (s ⊔ sucˡ ℓ)
Formula S ℓ = Formulaⁱ S ℓ []

infix 25 _⊨_

_⊨_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {ℓ : Level} → Program C α → Formula (Shape C) ℓ → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
x ⊨ f = x ⊨' desugar f ⦗ [] ⦘
  where
  negate-helper : {α : Set ℓ₁} → {β : Set ℓ₂} → {γ : Set ℓ₃} → {δ : Set ℓ₄} → {n : ℕ} → (xs : Vec (α × β × γ) n) → (f : β → δ) → map (proj₂ ∘ proj₂) (map (map₂ (map₁ f)) xs) ≡ map (proj₂ ∘ proj₂) xs
  negate-helper [] _ = refl
  negate-helper ((a , b , c) ∷ xs) f = helper refl (negate-helper xs f)
    where
    helper : {ℓ : Level} → {α : Set ℓ} → {x y : α} → {n : ℕ} → {xs ys : Vec α n} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
    helper {x = x} {y = y} {xs = xs} {ys = ys} fst snd = subst (λ a → x ∷ xs ≡ a ∷ ys) fst (subst (λ as → x ∷ xs ≡ x ∷ as) snd refl)

  ref-helper : {ℓ : Level} → {n : ℕ} → {i : Fin n} → {b : Bool} → {αs : List (Set ℓ)} → (xs : Vec (String × Bool × List (Set ℓ)) n) → (x : String) → find xs x _≟_ ≡ just (i , b , αs) → αs ≡ lookupᵛ (map (proj₂ ∘ proj₂) xs) i
  ref-helper ((x₁ , _ , _) ∷ xs) x h with x₁ ≟ x
  ref-helper ((x₁ , _ , _) ∷ xs) .x₁ refl | yes refl = refl
  ... | no _ with find xs x _≟_ | inspect (find xs x) _≟_
  ...   | just _ | [ eq ]⁼ with ref-helper xs x eq
  ref-helper ((x₁ , _ , _) ∷ xs) x refl | no _ | just _ | [ eq ]⁼ | refl = refl

  desugar : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (String × Bool × List (Set ℓ)) n} → Formulaⁱ S ℓ xs → Formula' S ℓ (map (proj₂ ∘ proj₂) xs)

  desugar-p : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (String × Bool × List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterizedⁱ S ℓ xs αs → Parameterized' S ℓ (map (proj₂ ∘ proj₂) xs) αs
  desugar-p (formula fⁱ) = formula desugar fⁱ
  desugar-p (α ＝ a ↦ pⁱ) = α ＝ a ↦ (desugar-p ∘ pⁱ)

  negate : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (String × Bool × List (Set ℓ)) n} → Formulaⁱ S ℓ xs → Formula' S ℓ (map (proj₂ ∘ proj₂) xs)

  negate-p : {n : ℕ} → {S : Set s} → {ℓ : Level} → {xs : Vec (String × Bool × List (Set ℓ)) n} → {αs : List (Set ℓ)} → Parameterizedⁱ S ℓ xs αs → Parameterized' S ℓ (map (proj₂ ∘ proj₂) xs) αs
  negate-p (formula fⁱ) = formula negate fⁱ
  negate-p (α ＝ a ↦ pⁱ) = α ＝ a ↦ (negate-p ∘ pⁱ)

  negate true = false
  negate false = true
  negate (val x) = val (¬ x)
  negate {S = S} {ℓ = ℓ} {xs = xs} (~ fⁱ) = subst (Formula' S ℓ) (negate-helper xs not) (desugar fⁱ)
  negate (fⁱ₁ ∧ fⁱ₂) = negate fⁱ₁ ∨ negate fⁱ₂
  negate (fⁱ₁ ∨ fⁱ₂) = negate fⁱ₁ ∧ negate fⁱ₂
  negate {S = S} {ℓ = ℓ} {xs = xs} (fⁱ₁ ⇒ fⁱ₂) = subst (Formula' S ℓ) (negate-helper xs not) (desugar fⁱ₁) ∧ negate fⁱ₂
  negate (∀⦗ α ⦘ fⁱ) = ∃⦗ α ⦘ (negate ∘ fⁱ)
  negate (∃⦗ α ⦘ fⁱ) = ∀⦗ α ⦘ (negate ∘ fⁱ)
  negate (⟨ rf ⟩ fⁱ) = [ desugar-rf rf ] negate fⁱ
  negate ([ rf ] fⁱ) = ⟨ desugar-rf rf ⟩ negate fⁱ
  negate (μ name ． pⁱ) = ν negate-p pⁱ
  negate (ν name ． pⁱ) = μ negate-p pⁱ
  negate {ℓ = ℓ} {xs = xs} ref name ⦗ args ⦘ with find xs name _≟_ | inspect (find xs name) _≟_
  ... | just (i , true , αs) | [ eq ]⁼ = ref i ⦗ subst (Arguments ℓ) (ref-helper xs name eq) args ⦘

  desugar true = true
  desugar false = false
  desugar (val x) = val x
  desugar {S = S} {ℓ = ℓ} {xs = xs} (~ fⁱ) = subst (Formula' S ℓ) (negate-helper xs not) (negate fⁱ)
  desugar (fⁱ₁ ∧ fⁱ₂) = desugar fⁱ₁ ∧ desugar fⁱ₂
  desugar (fⁱ₁ ∨ fⁱ₂) = desugar fⁱ₁ ∨ desugar fⁱ₂
  desugar {S = S} {ℓ = ℓ} {xs = xs} (fⁱ₁ ⇒ fⁱ₂) =  subst (Formula' S ℓ) (negate-helper xs not) (negate fⁱ₁) ∨ desugar fⁱ₂
  desugar (∀⦗ α ⦘ fⁱ) = ∀⦗ α ⦘ (desugar ∘ fⁱ)
  desugar (∃⦗ α ⦘ fⁱ) = ∃⦗ α ⦘ (desugar ∘ fⁱ)
  desugar (⟨ rf ⟩ fⁱ) = ⟨ desugar-rf rf ⟩ desugar fⁱ
  desugar ([ rf ] fⁱ) = [ desugar-rf rf ] desugar fⁱ
  desugar (μ name ． pⁱ) = μ desugar-p pⁱ
  desugar (ν name ． pⁱ) = ν desugar-p pⁱ
  desugar {ℓ = ℓ} {xs = xs} ref name ⦗ args ⦘ with find xs name _≟_ | inspect (find xs name) _≟_
  ... | just (i , true , αs) | [ eq ]⁼ = ref i ⦗ subst (Arguments ℓ) (ref-helper xs name eq) args ⦘
