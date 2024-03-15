{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.FixedPoints.Base where

open import Common.ActionFormulas using (ActionFormula; parseActF)
open import Common.FixedPoints using (Maybe'; Result; IndexedContainer; FixedPoint; WI; MI; _▷_)
open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; fromℕ<; inject₁; _↑ˡ_; _≟_)
open import Data.List using (List; lookup; length; findIndexᵇ)
open import Data.List.NonEmpty using (List⁺; _∷⁺_; foldr; toList) renaming ([_] to [_]⁺; map to map⁺; length to length⁺)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (n<1+n; m≤n⇒m≤n+o; +-assoc; +-identityʳ; +-suc)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax) renaming (map to mapᵖ)
open import Data.String using (String; _==_)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec using (Vec; _++_) renaming (lookup to lookupᵛ; map to mapᵛ)
open import Function using (case_of_; flip; id; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (yes; no)

open Maybe'
open Result
open IndexedContainer
open FixedPoint
open Bool
open _⋆_
open Fin
open List
open Maybe
open ℕ
open Vec

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
  flipRef x (var b i) with i ≟ x
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

  _↑_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → IndexedContainer C α n → (x : ℕ) → IndexedContainer C α (n + x)
  Shapeᵢ ((S ▷ _) ↑ x) = S
  Positionᵢ ((S ▷ P) ↑ x) s i with P s i
  ... | xs = map⁺ ((flip _↑'_) x) xs
    where
    _↑'_ : {C : Container ℓ₁ ℓ₂} → {α : Set ℓ₃} → {n : ℕ} → Result C α n → (x : ℕ) → Result C α (n + x)
    val (val (fst , snd)) ↑' x = val (val (fst , snd ↑ˡ x))
    val done ↑' _ = val done
    val fail ↑' _ = val fail
    exists s f ↑' x = exists s ((flip _↑'_) x ∘ f)
    all s f ↑' x = all s ((flip _↑'_) x ∘ f)

  data ModalitySequence (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
    ⟨_⟩_ [_]_ : ActionFormula C → ModalitySequence C → ModalitySequence C
    ε : ModalitySequence C

  unfold : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → {n : ℕ} → ModalitySequence C → C ⋆ α → (Maybe' (C ⋆ α) → Result C α n) → Result C α n
  unfold (⟨ _ ⟩ _) (pure _) f = f fail
  unfold (⟨ af ⟩ m) (impure (s , c)) f with parseActF af s
  ... | false = f fail
  ... | true = exists s λ p → unfold m (c p) f
  unfold ([ _ ] _) (pure _) f = f done
  unfold ([ af ] m) (impure (s , c)) f with parseActF af s
  ... | false = f done
  ... | true = all s λ p → unfold m (c p) f
  unfold ε x f = f (val x)

  containerize-var : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → Formulaᵈⁿᶠ-var C (suc n) → (n₁ : ℕ) → Vec (Fin (suc n₁)) (suc n) → (α : Set ℓ₃) → ModalitySequence C × Maybe' (∃[ n₂ ] (Fin (suc n₁ + n₂)) × Vec (FixedPoint × IndexedContainer C α (suc n₁ + n₂)) n₂)
  containerize-con : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → Formulaᵈⁿᶠ-con C (suc n) → (n₁ : ℕ) → Vec (Fin (suc n₁)) (suc n) → (α : Set ℓ₃) → ∃[ n₂ ] List⁺ (ModalitySequence C × Maybe' (Fin (suc n₁ + n₂))) × Vec (FixedPoint × IndexedContainer C α (suc n₁ + n₂)) n₂
  containerize-dis : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → Formulaᵈⁿᶠ-dis C (suc n) → (n₁ : ℕ) → Vec (Fin (suc n₁)) (suc n) → (α : Set ℓ₃) → ∃[ n₂ ] List⁺ (List⁺ (ModalitySequence C × Maybe' (Fin (suc n₁ + n₂)))) × Vec (FixedPoint × IndexedContainer C α (suc n₁ + n₂)) n₂
  containerize : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {n : ℕ} → FixedPoint → Formulaᵈⁿᶠ-dis C (suc n) → (n₁ : ℕ) → Vec (Fin n₁) n → (α : Set ℓ₃) → ∃[ n₂ ] Vec (FixedPoint × IndexedContainer C α (n₁ + suc n₂)) (suc n₂)

  containerize-var true _ _ _ = ε , done
  containerize-var false _ _ _ = ε , fail
  containerize-var (⟨ af ⟩ v) n₁ prev α with containerize-var v n₁ prev α
  ... | m , x = ⟨ af ⟩ m , x
  containerize-var ([ af ] v) n₁ prev α with containerize-var v n₁ prev α
  ... | m , x = [ af ] m , x
  containerize-var (μ d) n₁ prev α with containerize leastFP d (suc n₁) prev α
  ... | n₂ , Cs = ε , val (suc n₂ , subst Fin (sym (+-suc (suc n₁) n₂)) (fromℕ< (m≤n⇒m≤n+o n₂ (n<1+n (suc n₁)))) , Cs)
  containerize-var (ν d) n₁ prev α with containerize greatestFP d (suc n₁) prev α
  ... | n₂ , Cs = ε , val (suc n₂ , subst Fin (sym (+-suc (suc n₁) n₂)) (fromℕ< (m≤n⇒m≤n+o n₂ (n<1+n (suc n₁)))) , Cs)
  containerize-var (var i) n₁ prev α = ε , val (zero , subst Fin (sym (+-identityʳ (suc n₁))) (lookupᵛ prev i) , [])

  containerize-con (con-var v) n₁ prev α with containerize-var v n₁ prev α
  ... | m , val (n₂ , i , Cs) = n₂ , [ m , val i ]⁺ , Cs
  ... | m , done = zero , [ m , done ]⁺ , []
  ... | m , fail = zero , [ m , fail ]⁺ , []
  containerize-con (v ∧ c) n₁ prev α with containerize-var v n₁ prev α
  containerize-con {C = C} (v ∧ c) n₁ prev α | m , val (n₂ , i , Cs₁) with containerize-con c (n₁ + n₂) (mapᵛ ((flip _↑ˡ_) n₂) prev) α
  ... | n₃ , xs , Cs₂ = n₂ + n₃ , subst (λ n → List⁺ (ModalitySequence C × Maybe' (Fin n)) × Vec (FixedPoint × IndexedContainer C α n) (n₂ + n₃)) (+-assoc (suc n₁) n₂ n₃) ((m , val (fromℕ< (m≤n⇒m≤n+o n₃ (n<1+n (n₁ + n₂))))) ∷⁺ xs , mapᵛ (mapᵖ id ((flip _↑_) n₃)) Cs₁ ++ Cs₂)
  containerize-con (v ∧ c) n₁ prev α | m , done with containerize-con c n₁ prev α
  ... | n₂ , xs , Cs = n₂ , (m , done) ∷⁺ xs , Cs
  containerize-con (v ∧ c) n₁ prev α | m , fail with containerize-con c n₁ prev α
  ... | n₂ , xs , Cs = n₂ , (m , fail) ∷⁺ xs , Cs

  containerize-dis (dis-con c) n₁ prev α with containerize-con c n₁ prev α
  ... | n₂ , x , Cs = n₂ , [ x ]⁺ , Cs
  containerize-dis {C = C} (c ∨ d) n₁ prev α with containerize-con c n₁ prev α
  ... | n₂ , x , Cs₁ with containerize-dis d (n₁ + n₂) (mapᵛ ((flip _↑ˡ_) n₂) prev) α
  ...   | n₃ , xs , Cs₂ = n₂ + n₃ , subst (λ n → List⁺ (List⁺ (ModalitySequence C × Maybe' (Fin n))) × Vec (FixedPoint × IndexedContainer C α n) (n₂ + n₃)) (+-assoc (suc n₁) n₂ n₃) (map⁺ (mapᵖ id λ { (val x) → val (x ↑ˡ n₃) ; done → done ; fail → fail }) x ∷⁺ xs , mapᵛ (mapᵖ id ((flip _↑_) n₃)) Cs₁ ++ Cs₂)

  containerize {C = C} fp d n₁ prev α with containerize-dis d n₁ (fromℕ< (n<1+n n₁) ∷ mapᵛ inject₁ prev) α
  ... | n₂ , xs , Cs = n₂ , subst (λ n → Vec (FixedPoint × IndexedContainer C α n) (suc n₂)) (sym (+-suc n₁ n₂)) ((fp , container) ∷ Cs)
    where
    container : IndexedContainer C α (suc n₁ + n₂)
    Shapeᵢ container = length⁺ xs
    Positionᵢ container s i = foldr (_∷⁺_ ∘ λ (m , n) → position m i n) (λ (m , n) → [ position m i n ]⁺) (lookup (toList xs) s)
      where
      position : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → {n : ℕ} → ModalitySequence C → C ⋆ α → Maybe' (Fin n) → Result C α n
      position m i (val n) = unfold m i λ { (val o) → val (val (o , n)) ; done → val done ; fail → val fail }
      position m i done = unfold m i λ { (val _) → val done ; done → val done ; fail → val fail }
      position m i fail = unfold m i λ { (val _) → val fail ; done → val done ; fail → val fail }

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
  _⊩ᵛ_ {α = α} (μ d) x = WI (proj₂ (containerize leastFP d zero [] α)) (val (x , zero))
  _⊩ᵛ_ {α = α} (ν d) x = MI (proj₂ (containerize greatestFP d zero [] α)) (val (x , zero))

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
