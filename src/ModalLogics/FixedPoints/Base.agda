{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.FixedPoints.Base where

open import Common.ActionFormulas using (ActionFormula; parseActF)
open import Common.FixedPoints using (Maybe'; IndexedContainer; FixedPoint; WI; MI)
open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin) renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; lookup; length; findIndexᵇ; _++_)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; foldr; toList) renaming (length to length⁺; [_] to [_]⁺)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String; _==_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; _∷_) renaming ([_] to [_]ᵛ; lookup to lookupᵛ)
open import Function using (case_of_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no)

open Maybe'
open IndexedContainer
open FixedPoint
open Bool
open _⋆_
open Fin
open List
open Maybe
open ℕ

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 40 ~_
infix 40 var
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_
infix 30 μ_．_
infix 30 ν_．_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ~_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : ActionFormula C → Formula C → Formula C
  μ_．_ ν_．_ : String → Formula C → Formula C
  var : String → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
f ⊩ x = case f→f' f [] of λ { (just f') → case f''→fᵈⁿᶠ (f'→f'' f') of λ { (just d) → d ⊩ᵈ x ; nothing → ⊥ } ; nothing → ⊥ }
  where
  infix 40 ~_
  infix 40 var
  infixr 35 _∧_
  infixr 35 _∨_
  infixr 35 _⇒_
  infix 30 ⟨_⟩_
  infix 30 [_]_
  infix 30 μ_
  infix 30 ν_

  data Formula' (C : Container ℓ₁ ℓ₂) : ℕ → Set ℓ₁ where
    true false : ∀ {n} → Formula' C n
    ~_ : ∀ {n} → Formula' C n → Formula' C n
    _∧_ _∨_ _⇒_ : ∀ {n} → Formula' C n → Formula' C n → Formula' C n
    ⟨_⟩_ [_]_ : ∀ {n} → ActionFormula C → Formula' C n → Formula' C n
    μ_ ν_ : ∀ {n} → Formula' C (suc n) → Formula' C n
    var : ∀ {n} → Fin n → Formula' C n

  f→f' : {C : Container ℓ₁ ℓ₂} → Formula C → (xs : List String) → Maybe (Formula' C (length xs))
  f→f' true xs = just true
  f→f' false xs = just false
  f→f' (~ f) xs with f→f' f xs
  ... | just f' = just (~ f')
  ... | nothing = nothing
  f→f' (f₁ ∧ f₂) xs with f→f' f₁ xs | f→f' f₂ xs
  ... | just f'₁ | just f'₂ = just (f'₁ ∧ f'₂)
  ... | _ | _ = nothing
  f→f' (f₁ ∨ f₂) xs with f→f' f₁ xs | f→f' f₂ xs
  ... | just f'₁ | just f'₂ = just (f'₁ ∨ f'₂)
  ... | _ | _ = nothing
  f→f' (f₁ ⇒ f₂) xs with f→f' f₁ xs | f→f' f₂ xs
  ... | just f'₁ | just f'₂ = just (f'₁ ⇒ f'₂)
  ... | _ | _ = nothing
  f→f' (⟨ af ⟩ f) xs with f→f' f xs
  ... | just f' = just (⟨ af ⟩ f')
  ... | nothing = nothing
  f→f' ([ af ] f) xs with f→f' f xs
  ... | just f' = just ([ af ] f')
  ... | nothing = nothing
  f→f' (μ x ． f) xs with f→f' f (x ∷ xs)
  ... | just f' = just (μ f')
  ... | nothing = nothing
  f→f' (ν x ． f) xs with f→f' f (x ∷ xs)
  ... | just f' = just (ν f')
  ... | nothing = nothing
  f→f' (var x) xs with findIndexᵇ (_==_ x) xs
  ... | just i = just (var i)
  ... | nothing = nothing

  data Formula'' (C : Container ℓ₁ ℓ₂) : ℕ → Set ℓ₁ where
    true false : ∀ {n} → Formula'' C n
    _∧_ _∨_ : ∀ {n} → Formula'' C n → Formula'' C n → Formula'' C n
    ⟨_⟩_ [_]_ : ∀ {n} → ActionFormula C → Formula'' C n → Formula'' C n
    μ_ ν_ : ∀ {n} → Formula'' C (suc n) → Formula'' C n
    var : ∀ {n} → Bool → Fin n → Formula'' C n

  flipRef : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Fin n → Formula'' C n → Formula'' C n
  flipRef _ true = true
  flipRef _ false = false
  flipRef x (f''₁ ∧ f''₂) = flipRef x f''₁ ∧ flipRef x f''₂
  flipRef x (f''₁ ∨ f''₂) = flipRef x f''₁ ∨ flipRef x f''₂
  flipRef x (⟨ af ⟩ f'') = ⟨ af ⟩ flipRef x f''
  flipRef x ([ af ] f'') = [ af ] flipRef x f''
  flipRef x (μ f'') = μ flipRef (suc x) f''
  flipRef x (ν f'') = ν flipRef (suc x) f''
  flipRef x (var b i) with i ≟ᶠ x
  ... | no _ = var b i
  ... | yes _ = var (not b) i

  negate : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formula'' C n → Formula'' C n
  negate true = false
  negate false = true
  negate (f''₁ ∧ f''₂) = negate f''₁ ∨ negate f''₂
  negate (f''₁ ∨ f''₂) = negate f''₁ ∧ negate f''₂
  negate (⟨ af ⟩ f'') = [ af ] negate f''
  negate ([ af ] f'') = ⟨ af ⟩ negate f''
  negate (μ f'') = ν flipRef zero f''
  negate (ν f'') = μ flipRef zero f''
  negate (var b i) = var (not b) i

  f'→f'' : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formula' C n → Formula'' C n
  f'→f'' true = true
  f'→f'' false = false
  f'→f'' (~ f') = negate (f'→f'' f')
  f'→f'' (f'₁ ∧ f'₂) = f'→f'' f'₁ ∧ f'→f'' f'₂
  f'→f'' (f'₁ ∨ f'₂) = f'→f'' f'₁ ∨ f'→f'' f'₂
  f'→f'' (f'₁ ⇒ f'₂) = negate (f'→f'' f'₁) ∨ f'→f'' f'₂
  f'→f'' (⟨ af ⟩ f') = ⟨ af ⟩ f'→f'' f'
  f'→f'' ([ af ] f') = [ af ] f'→f'' f'
  f'→f'' (μ f') = μ f'→f'' f'
  f'→f'' (ν f') = ν f'→f'' f'
  f'→f'' (var i) = var true i

  data Formulaᵈⁿᶠ-var (C : Container ℓ₁ ℓ₂) : ℕ → Set ℓ₁
  data Formulaᵈⁿᶠ-con (C : Container ℓ₁ ℓ₂) : ℕ → Set ℓ₁
  data Formulaᵈⁿᶠ-dis (C : Container ℓ₁ ℓ₂) : ℕ → Set ℓ₁

  data Formulaᵈⁿᶠ-var C where
    true false : ∀ {n} → Formulaᵈⁿᶠ-var C n
    ⟨_⟩_ [_]_ : ∀ {n} → ActionFormula C → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-var C n
    μ_ ν_ : ∀ {n} → Formulaᵈⁿᶠ-dis C (suc n) → Formulaᵈⁿᶠ-var C n
    var : ∀ {n} → Fin n → Formulaᵈⁿᶠ-var C n

  data Formulaᵈⁿᶠ-con C where
    con-var : ∀ {n} → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-con C n
    _∧_ : ∀ {n} → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n

  data Formulaᵈⁿᶠ-dis C where
    dis-con : ∀ {n} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-dis C n
    _∨_ : ∀ {n} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n

  merge-dis-dis-or : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
  merge-dis-dis-or (dis-con c) d = c ∨ d
  merge-dis-dis-or (c ∨ d₁) d₂ = c ∨ merge-dis-dis-or d₁ d₂

  merge-con-con : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n
  merge-con-con (con-var v) c = v ∧ c
  merge-con-con (v ∧ c₁) c₂ = v ∧ merge-con-con c₁ c₂

  merge-con-dis : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
  merge-con-dis c₁ (dis-con c₂) = dis-con (merge-con-con c₁ c₂)
  merge-con-dis c₁ (c₂ ∨ d₂) = merge-con-con c₁ c₂ ∨ merge-con-dis c₁ d₂

  merge-dis-dis-and : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
  merge-dis-dis-and (dis-con c) d = merge-con-dis c d
  merge-dis-dis-and (c ∨ d₁) d₂ = merge-dis-dis-or (merge-con-dis c d₂) (merge-dis-dis-and d₁ d₂)

  f''→fᵈⁿᶠ : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → Formula'' C n → Maybe (Formulaᵈⁿᶠ-dis C n)
  f''→fᵈⁿᶠ true = just (dis-con (con-var true))
  f''→fᵈⁿᶠ false = just (dis-con (con-var false))
  f''→fᵈⁿᶠ (f''₁ ∧ f''₂) with f''→fᵈⁿᶠ f''₁ | f''→fᵈⁿᶠ f''₂
  ... | just d₁ | just d₂ = just (merge-dis-dis-and d₁ d₂)
  ... | _ | _ = nothing
  f''→fᵈⁿᶠ (f''₁ ∨ f''₂) with f''→fᵈⁿᶠ f''₁ | f''→fᵈⁿᶠ f''₂
  ... | just d₁ | just d₂ = just (merge-dis-dis-or d₁ d₂)
  ... | _ | _ = nothing
  f''→fᵈⁿᶠ (⟨ af ⟩ f'') with f''→fᵈⁿᶠ f''
  ... | just d = just (merge-∃-dis af d)
    where
    merge-∃-var : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-var C n
    merge-∃-var af v = ⟨ af ⟩ v

    merge-∃-con : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n
    merge-∃-con af (con-var v) = con-var (merge-∃-var af v)
    merge-∃-con af (v ∧ c) = merge-∃-var af v ∧ merge-∃-con af c

    merge-∃-dis : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
    merge-∃-dis af (dis-con c) = dis-con (merge-∃-con af c)
    merge-∃-dis af (c ∨ d) = merge-∃-con af c ∨ merge-∃-dis af d
  ... | _ = nothing
  f''→fᵈⁿᶠ ([ af ] f'') with f''→fᵈⁿᶠ f''
  ... | just d = just (merge-∀-dis af d)
    where
    merge-∀-var : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-var C n → Formulaᵈⁿᶠ-var C n
    merge-∀-var af v = [ af ] v

    merge-∀-con : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-con C n → Formulaᵈⁿᶠ-con C n
    merge-∀-con af (con-var v) = con-var (merge-∀-var af v)
    merge-∀-con af (v ∧ c) = merge-∀-var af v ∧ merge-∀-con af c

    merge-∀-dis : {C : Container ℓ₁ ℓ₂} → {n : ℕ} → ActionFormula C → Formulaᵈⁿᶠ-dis C n → Formulaᵈⁿᶠ-dis C n
    merge-∀-dis af (dis-con c) = dis-con (merge-∀-con af c)
    merge-∀-dis af (c ∨ d) = merge-∀-con af c ∨ merge-∀-dis af d
  ... | _ = nothing
  f''→fᵈⁿᶠ (μ f'') with f''→fᵈⁿᶠ f''
  ... | just d = just (dis-con (con-var (μ d)))
  ... | _ = nothing
  f''→fᵈⁿᶠ (ν f'') with f''→fᵈⁿᶠ f''
  ... | just d = just (dis-con (con-var (ν d)))
  ... | _ = nothing
  f''→fᵈⁿᶠ (var false _) = nothing
  f''→fᵈⁿᶠ (var true i) = just (dis-con (con-var (var i)))

  data ModalitySequence (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
    ⟨_⟩_ [_]_ : ActionFormula C → ModalitySequence C → ModalitySequence C
    ε : ModalitySequence C

  unfold : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → ModalitySequence C → C ⋆ α → (Maybe' (C ⋆ α) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  unfold (⟨ _ ⟩ _) (pure _) f = f fail
  unfold (⟨ af ⟩ m) (impure (s , c)) f with parseActF af s
  ... | false = f fail
  ... | true = ∃[ p ] unfold m (c p) f
  unfold ([ _ ] _) (pure _) f = f done
  unfold ([ af ] m) (impure (s , c)) f with parseActF af s
  ... | false = f done
  ... | true = ∀ p → unfold m (c p) f
  unfold ε x f = f (val x)

  containerize-var : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → (α : Set ℓ₃) → Vec ℕ (suc n) → ℕ → Formulaᵈⁿᶠ-var C (suc n) → ModalitySequence C × Maybe' (ℕ × List (FixedPoint × IndexedContainer (C ⋆ α)))
  containerize-con : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → (α : Set ℓ₃) → Vec ℕ (suc n) → ℕ → Formulaᵈⁿᶠ-con C (suc n) → List⁺ (ModalitySequence C × Maybe' ℕ) × List (FixedPoint × IndexedContainer (C ⋆ α))
  containerize-dis : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → (α : Set ℓ₃) → Vec ℕ (suc n) → ℕ → Formulaᵈⁿᶠ-dis C (suc n) → List⁺ (List⁺ (ModalitySequence C × Maybe' ℕ)) × List (FixedPoint × IndexedContainer (C ⋆ α))
  containerize : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → (α : Set ℓ₃) → Vec ℕ (suc n) → ℕ → FixedPoint → Formulaᵈⁿᶠ-dis C (suc n) → List⁺ (FixedPoint × IndexedContainer (C ⋆ α))

  containerize-var α prev i true = ε , done
  containerize-var α prev i false = ε , fail
  containerize-var α prev i (⟨ s ⟩ v) with containerize-var α prev i v
  ... | m , x = ⟨ s ⟩ m , x
  containerize-var α prev i ([ s ] v) with containerize-var α prev i v
  ... | m , x = [ s ] m , x
  containerize-var α prev i (μ d) = ε , val (i , toList (containerize α (i ∷ prev) (suc i) leastFP d))
  containerize-var α prev i (ν d) = ε , val (i , toList (containerize α (i ∷ prev) (suc i) greatestFP d))
  containerize-var α prev _ (var n) = ε , val (lookupᵛ prev n , [])

  containerize-con α prev i (con-var v) with containerize-var α prev i v
  ... | m , val (n , Cs) = [ m , val n ]⁺ , Cs
  ... | m , done = [ m , done ]⁺ , []
  ... | m , fail = [ m , fail ]⁺ , []
  containerize-con α prev i (v ∧ c) with containerize-var α prev i v
  containerize-con α prev i (v ∧ c) | m , val (n , Cs₁) with containerize-con α prev (i + length Cs₁) c
  ... | xs , Cs₂ = (m , val n) ∷⁺ xs , Cs₁ ++ Cs₂
  containerize-con α prev i (v ∧ c) | m , done with containerize-con α prev i c
  ... | xs , Cs = (m , done) ∷⁺ xs , Cs
  containerize-con α prev i (v ∧ c) | m , fail with containerize-con α prev i c
  ... | xs , Cs = (m , fail) ∷⁺ xs , Cs

  containerize-dis α prev i (dis-con c) with containerize-con α prev i c
  ... | x , Cs = [ x ]⁺ , Cs
  containerize-dis α prev i (c ∨ d) with containerize-con α prev i c
  ... | x , Cs₁ with containerize-dis α prev (i + length Cs₁) d
  ...   | xs , Cs₂ = x ∷⁺ xs , Cs₁ ++ Cs₂

  containerize {C = C} α prev i fp d with containerize-dis α prev i d
  ... | xs , Cs = (fp , container) ∷ Cs
    where
    container : IndexedContainer (C ⋆ α)
    Shape container = length⁺ xs
    Position container s i o = foldr (λ { (m , n) acc → position m n i o ⊎ acc }) (λ { (m , n) → position m n i o }) (lookup (toList xs) s)
      where
      position : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → ModalitySequence C → Maybe' ℕ → C ⋆ α → Maybe' ((C ⋆ α) × ℕ) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
      position m (val n) i o = unfold m i λ { (val res) → o ≡ val (res , n) ; done → o ≡ done ; fail → o ≡ fail }
      position m done i o = unfold m i λ { (val _) → o ≡ done ; done → o ≡ done ; fail → o ≡ fail }
      position m fail i o = unfold m i λ { (val _) → o ≡ fail ; done → o ≡ done ; fail → o ≡ fail }

  infix 25 _⊩ᵛ_
  infix 25 _⊩ᶜ_
  infix 25 _⊩ᵈ_

  _⊩ᵛ_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-var C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  _⊩ᶜ_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-con C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  _⊩ᵈ_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-dis C zero → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

  true ⊩ᵛ _ = ⊤
  false ⊩ᵛ _ = ⊥
  ⟨ _ ⟩ _ ⊩ᵛ pure _ = ⊥
  ⟨ af ⟩ v ⊩ᵛ impure (s , c) with parseActF af s
  ... | false = ⊥
  ... | true = ∃[ p ] v ⊩ᵛ c p
  [ _ ] _ ⊩ᵛ pure _ = ⊤
  [ af ] v ⊩ᵛ impure (s , c) with parseActF af s
  ... | false = ⊤
  ... | true = ∀ p → v ⊩ᵛ c p
  _⊩ᵛ_ {α = α} (μ d) x = WI (containerize α [ zero ]ᵛ (suc zero) leastFP d) (val (x , zero))
  _⊩ᵛ_ {α = α} (ν d) x = MI (containerize α [ zero ]ᵛ (suc zero) greatestFP d) (val (x , zero))

  con-var v ⊩ᶜ x = v ⊩ᵛ x
  v ∧ c ⊩ᶜ x = (v ⊩ᵛ x) × (c ⊩ᶜ x)

  dis-con c ⊩ᵈ x = c ⊩ᶜ x
  c ∨ d ⊩ᵈ x = (c ⊩ᶜ x) ⊎ (d ⊩ᵈ x)

infix 25 _⊩_!_

_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula C → Program C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
f ⊩ x ! i = f ⊩ x i

infix 25 _▸_⊩_!_

_▸_⊩_!_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula C → RecursiveProgram C I O → I → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₄)
n ▸ f ⊩ x ! i = f ⊩ (recursionHandler x n) i
