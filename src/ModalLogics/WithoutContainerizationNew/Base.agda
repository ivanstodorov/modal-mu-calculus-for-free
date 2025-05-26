{-# OPTIONS --without-K --safe --guardedness #-}
module ModalLogics.WithoutContainerizationNew.Base where

open import Common.Program using (impure; pure; free; Program)
open import Common.RegularFormulasWithData using (ActionFormula; RegularFormula; _∈_)
open import Data.Bool using (Bool; not)
open import Data.Container using (Container)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; length; map)
open import Data.List.NonEmpty using (List⁺; head) renaming (_∷_ to _∷⁺_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; _×_; Σ-syntax)
open import Function using (case_of_; _∘_)
open import Level using (Level; _⊔_) renaming (suc to sucˡ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open RegularFormula
open Bool
open Container
open Fin
open List
open Maybe

private variable
  a s p r : Level

lookup : {α : Set a} → {n : ℕ} → (xs : List α) → (i : Fin n) → Maybe α
lookup [] i = nothing
lookup (x ∷ _) zero = just x
lookup (_ ∷ xs) (suc i) = lookup xs i

drop : {α : Set a} → (xs : List α) → (i : Fin (length xs)) → List⁺ α
drop (x ∷ xs) zero = x ∷⁺ xs
drop (_ ∷ xs) (suc i) = drop xs i

data Arguments (ℓ : Level) : List (Set ℓ) → Set (sucˡ ℓ) where
  [] : Arguments ℓ []
  _∷_ : ∀ {params T} → T → Arguments ℓ params → Arguments ℓ (T ∷ params)

get-args : {ℓ : Level} → (params⁺ : List (Σ[ T ∈ Set ℓ ] T)) → Arguments ℓ (map proj₁ params⁺)
get-args [] = []
get-args ((_ , t) ∷ params⁺) = t ∷ get-args params⁺

infix 60 val_
infix 60 lift_
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

data Formulaⁱ (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → List Bool → Set (a ⊔ sucˡ ℓ)

infix 70 formula_
infix 65 intro_

data FixedPointⁱ (α : Set a) (ℓ : Level) (prev : List (List (Set ℓ))) (flags : List Bool) : List (Set ℓ) → Set (a ⊔ sucˡ ℓ) where
  formula_ : Formulaⁱ α ℓ prev flags → FixedPointⁱ α ℓ prev flags []
  intro_ : ∀ {params T} → (T → FixedPointⁱ α ℓ prev flags params) → FixedPointⁱ α ℓ prev flags (T ∷ params)

data Formulaⁱ α ℓ where
  true false : ∀ {prev flags} → Formulaⁱ α ℓ prev flags
  val_ : ∀ {prev flags} → Set ℓ → Formulaⁱ α ℓ prev flags
  lift_ : ∀ {prev flags params flag} → Formulaⁱ α ℓ prev flags → Formulaⁱ α ℓ (params ∷ prev) (flag ∷ flags)
  ~_ : ∀ {prev flags} → Formulaⁱ α ℓ prev (map not flags) → Formulaⁱ α ℓ prev flags
  _∧_ _∨_ : ∀ {prev flags} → Formulaⁱ α ℓ prev flags → Formulaⁱ α ℓ prev flags → Formulaⁱ α ℓ prev flags
  _⇒_ : ∀ {prev flags} → Formulaⁱ α ℓ prev (map not flags) → Formulaⁱ α ℓ prev flags → Formulaⁱ α ℓ prev flags
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {prev flags} → (T : Set ℓ) → (T → Formulaⁱ α ℓ prev flags) → Formulaⁱ α ℓ prev flags
  ⟨_⟩_ [_]_ : ∀ {prev flags} → RegularFormula α ℓ → Formulaⁱ α ℓ prev flags → Formulaⁱ α ℓ prev flags
  μ_．_ ν_．_ : ∀ {prev flags} → (params⁺ : List (Σ[ T ∈ Set ℓ ] T)) → (let params = map proj₁ params⁺ in FixedPointⁱ α ℓ (params ∷ prev) (true ∷ flags) params) → Formulaⁱ α ℓ prev flags
  ref_⦗_⦘ : ∀ {prev flags} → (i : Fin (length prev)) → case lookup flags i of (λ { (just true) → Arguments ℓ (head (drop prev i))
                                                                                 ; _ → ⊥ }) → Formulaⁱ α ℓ prev flags

data Formula' (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → Set (a ⊔ sucˡ ℓ)

data FixedPoint' (α : Set a) (ℓ : Level) (prev : List (List (Set ℓ))) : List (Set ℓ) → Set (a ⊔ sucˡ ℓ) where
  formula_ : Formula' α ℓ prev → FixedPoint' α ℓ prev []
  intro_ : ∀ {params T} → (T → FixedPoint' α ℓ prev params) → FixedPoint' α ℓ prev (T ∷ params)

data Formula' α ℓ where
  true false : ∀ {prev} → Formula' α ℓ prev
  val_ : ∀ {prev} → Set ℓ → Formula' α ℓ prev
  lift_ : ∀ {prev params} → Formula' α ℓ prev → Formula' α ℓ (params ∷ prev)
  _∧_ _∨_ : ∀ {prev} → Formula' α ℓ prev → Formula' α ℓ prev → Formula' α ℓ prev
  ∀⦗_⦘_ ∃⦗_⦘_ : ∀ {prev} → (T : Set ℓ) → (T → Formula' α ℓ prev) → Formula' α ℓ prev
  ⟨_⟩_ [_]_ : ∀ {prev} → ActionFormula α ℓ → Formula' α ℓ prev → Formula' α ℓ prev
  μ_．_ ν_．_ : ∀ {prev} → (params⁺ : List (Σ[ T ∈ Set ℓ ] T)) → (let params = map proj₁ params⁺ in FixedPoint' α ℓ (params ∷ prev) params) → Formula' α ℓ prev
  ref_⦗_⦘ : ∀ {prev} → (i : Fin (length prev)) → Arguments ℓ (head (drop prev i)) → Formula' α ℓ prev

_⟮_⟯ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {params : List (Set ℓ)} → FixedPoint' α ℓ prev params → Arguments ℓ params → Formula' α ℓ prev
(formula f') ⟮ [] ⟯ = f'
(intro fp') ⟮ t ∷ args ⟯ = fp' t ⟮ args ⟯

data ActionTree (α : Set a) (ℓ : Level) : Set (a ⊔ sucˡ ℓ)

data ActionNode (α : Set a) (ℓ : Level) : Set (a ⊔ sucˡ ℓ) where
  actF_ : ActionFormula α ℓ → ActionNode α ℓ
  _* : ActionTree α ℓ → ActionNode α ℓ

data ActionTree α ℓ where
  ⦗_⦘ : ActionNode α ℓ → ActionTree α ℓ
  _·_ : ActionNode α ℓ → ActionTree α ℓ → ActionTree α ℓ
  +ˡ : ActionTree α ℓ → ActionTree α ℓ
  +ʳ : ActionTree α ℓ → ActionTree α ℓ
  _+_ : ActionTree α ℓ → ActionTree α ℓ → ActionTree α ℓ

concatenate : {α : Set a} → {ℓ : Level} → ActionTree α ℓ → ActionTree α ℓ → ActionTree α ℓ
concatenate ⦗ x ⦘ at₂ = x · at₂
concatenate (x · at₁) at₂ = x · concatenate at₁ at₂
concatenate (+ˡ at₁) at₂ = concatenate at₁ at₂ + at₂
concatenate (+ʳ at₁) at₂ = at₂ + concatenate at₁ at₂
concatenate (at₁ + at₂) at₃ = concatenate at₁ at₃ + concatenate at₂ at₃

rf→at : {α : Set a} → {ℓ : Level} → RegularFormula α ℓ → Maybe (ActionTree α ℓ)
rf→at ε = nothing
rf→at (actF af) = just ⦗ actF af ⦘
rf→at (rf₁ · rf₂) with rf→at rf₁ | rf→at rf₂
... | just at₁ | just at₂ = just (concatenate at₁ at₂)
... | just at₁ | nothing = just at₁
... | nothing | just at₂ = just at₂
... | nothing | nothing = nothing
rf→at (rf₁ + rf₂) with rf→at rf₁ | rf→at rf₂
... | just at₁ | just at₂ = just (at₁ + at₂)
... | just at₁ | nothing = just (+ˡ at₁)
... | nothing | just at₂ = just (+ʳ at₂)
... | nothing | nothing = nothing
rf→at (rf *) with rf→at rf
... | just at = just ⦗ at * ⦘
... | nothing = nothing
rf→at (rf ⁺) with rf→at rf
... | just at = just (concatenate at ⦗ at * ⦘)
... | nothing = nothing

at→af-∃ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → ActionTree α ℓ → Formula' α ℓ prev → Formula' α ℓ prev
at→af-∃ ⦗ actF af ⦘ f' = ⟨ af ⟩ f'
at→af-∃ {prev = prev} ⦗ at * ⦘ f' = μ [] ． (formula (at→af-∃ at ref zero ⦗ [] ⦘ ∨ lift f'))
at→af-∃ ((actF af) · at) f' = ⟨ af ⟩ at→af-∃ at f'
at→af-∃ {prev = prev} ((at₁ *) · at₂) f' = μ [] ． (formula (at→af-∃ at₁ ref zero ⦗ [] ⦘ ∨ lift at→af-∃ at₂ f'))
at→af-∃ (+ˡ at) f' = at→af-∃ at f' ∨ f'
at→af-∃ (+ʳ at) f' = f' ∨ at→af-∃ at f'
at→af-∃ (at₁ + at₂) f' = at→af-∃ at₁ f' ∨ at→af-∃ at₂ f'

at→af-∀ : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → ActionTree α ℓ → Formula' α ℓ prev → Formula' α ℓ prev
at→af-∀ ⦗ actF af ⦘ f' = [ af ] f'
at→af-∀ {prev = prev} ⦗ at * ⦘ f' = ν [] ． (formula (at→af-∀ at ref zero ⦗ [] ⦘ ∧ lift f'))
at→af-∀ ((actF af) · at) f' = [ af ] at→af-∀ at f'
at→af-∀ {prev = prev} ((at₁ *) · at₂) f' = ν [] ． (formula (at→af-∀ at₁ ref zero ⦗ [] ⦘ ∧ lift at→af-∀ at₂ f'))
at→af-∀ (+ˡ at) f' = at→af-∀ at f' ∧ f'
at→af-∀ (+ʳ at) f' = f' ∧ at→af-∀ at f'
at→af-∀ (at₁ + at₂) f' = at→af-∀ at₁ f' ∧ at→af-∀ at₂ f'

fⁱ→f' : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {flags : List Bool} → Formulaⁱ α ℓ prev flags → Formula' α ℓ prev

fpⁱ→fp' : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {flags : List Bool} → {params : List (Set ℓ)} → FixedPointⁱ α ℓ prev flags params → FixedPoint' α ℓ prev params
fpⁱ→fp' (formula fⁱ) = formula fⁱ→f' fⁱ
fpⁱ→fp' (intro fpⁱ) = intro (fpⁱ→fp' ∘ fpⁱ)

negate : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {flags : List Bool} → Formulaⁱ α ℓ prev flags → Formula' α ℓ prev

negate-fp : {α : Set a} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {flags : List Bool} → {params : List (Set ℓ)} → FixedPointⁱ α ℓ prev flags params → FixedPoint' α ℓ prev params
negate-fp (formula fⁱ) = formula negate fⁱ
negate-fp (intro fpⁱ) = intro (negate-fp ∘ fpⁱ)

negate true = false
negate false = true
negate (val T) = val (¬ T)
negate (lift fⁱ) = lift negate fⁱ
negate (~ fⁱ) = fⁱ→f' fⁱ
negate (fⁱ₁ ∧ fⁱ₂) = negate fⁱ₁ ∨ negate fⁱ₂
negate (fⁱ₁ ∨ fⁱ₂) = negate fⁱ₁ ∧ negate fⁱ₂
negate (fⁱ₁ ⇒ fⁱ₂) = fⁱ→f' fⁱ₁ ∧ negate fⁱ₂
negate (∀⦗ T ⦘ fⁱ) = ∃⦗ T ⦘ (negate ∘ fⁱ)
negate (∃⦗ T ⦘ fⁱ) = ∀⦗ T ⦘ (negate ∘ fⁱ)
negate (⟨ rf ⟩ fⁱ) with rf→at rf
... | just at = at→af-∀ at (negate fⁱ)
... | nothing = negate fⁱ
negate ([ rf ] fⁱ) with rf→at rf
... | just at = at→af-∃ at (negate fⁱ)
... | nothing = negate fⁱ
negate (μ params⁺ ． fpⁱ) = ν params⁺ ． negate-fp fpⁱ
negate (ν params⁺ ． fpⁱ) = μ params⁺ ． negate-fp fpⁱ
negate {flags = flags} ref i ⦗ args ⦘ with lookup flags i
... | just true = ref i ⦗ args ⦘

fⁱ→f' true = true
fⁱ→f' false = false
fⁱ→f' (val T) = val T
fⁱ→f' (lift fⁱ) = lift fⁱ→f' fⁱ
fⁱ→f' (~ fⁱ) = negate fⁱ
fⁱ→f' (fⁱ₁ ∧ fⁱ₂) = fⁱ→f' fⁱ₁ ∧ fⁱ→f' fⁱ₂
fⁱ→f' (fⁱ₁ ∨ fⁱ₂) = fⁱ→f' fⁱ₁ ∨ fⁱ→f' fⁱ₂
fⁱ→f' (fⁱ₁ ⇒ fⁱ₂) = negate fⁱ₁ ∨ fⁱ→f' fⁱ₂
fⁱ→f' (∀⦗ T ⦘ fⁱ) = ∀⦗ T ⦘ (fⁱ→f' ∘ fⁱ)
fⁱ→f' (∃⦗ T ⦘ fⁱ) = ∃⦗ T ⦘ (fⁱ→f' ∘ fⁱ)
fⁱ→f' (⟨ rf ⟩ fⁱ) with rf→at rf
... | just at = at→af-∃ at (fⁱ→f' fⁱ)
... | nothing = fⁱ→f' fⁱ
fⁱ→f' ([ rf ] fⁱ) with rf→at rf
... | just at = at→af-∀ at (fⁱ→f' fⁱ)
... | nothing = fⁱ→f' fⁱ
fⁱ→f' (μ params⁺ ． fpⁱ) = μ params⁺ ． fpⁱ→fp' fpⁱ
fⁱ→f' (ν params⁺ ． fpⁱ) = ν params⁺ ． fpⁱ→fp' fpⁱ
fⁱ→f' {flags = flags} ref i ⦗ args ⦘ with lookup flags i
... | just true = ref i ⦗ args ⦘

Formula : Set a → (ℓ : Level) → Set (a ⊔ sucˡ ℓ)
Formula α ℓ = Formulaⁱ α ℓ [] []

data Context (α : Set a) (ℓ : Level) : List (List (Set ℓ)) → Set (a ⊔ sucˡ ℓ) where
  [] : Context α ℓ []
  _∷_ : ∀ {prev : List (List (Set ℓ))} {params : List (Set ℓ)} → Bool × FixedPoint' α ℓ (params ∷ prev) params → Context α ℓ prev → Context α ℓ (params ∷ prev)

infix 25 _⊢_⊨'_

data _⊢_⊨'_ {C : Container s p} {R : Set r} {ℓ : Level} : {prev : List (List (Set ℓ))} → Context (Shape C) ℓ prev → Program C R → Formula' (Shape C) ℓ prev → Set (s ⊔ p ⊔ r ⊔ sucˡ ℓ)

record Mu {C : Container s p} {R : Set r} {ℓ : Level} {params : List (Set ℓ)} {prev : List (List (Set ℓ))} (Γ : Context (Shape C) ℓ prev) (x : Program C R) (fp' : FixedPoint' (Shape C) ℓ (params ∷ prev) params) (args : Arguments ℓ params) : Set (s ⊔ p ⊔ r ⊔ sucˡ ℓ) where
  inductive
  constructor muᶜ
  field
    mu : ((false , fp') ∷ Γ) ⊢ x ⊨' (fp' ⟮ args ⟯)

record Nu {C : Container s p} {R : Set r} {ℓ : Level} {params : List (Set ℓ)} {prev : List (List (Set ℓ))} (Γ : Context (Shape C) ℓ prev) (x : Program C R) (fp' : FixedPoint' (Shape C) ℓ (params ∷ prev) params) (args : Arguments ℓ params) : Set (s ⊔ p ⊔ r ⊔ sucˡ ℓ) where
  coinductive
  constructor nuᶜ
  field
    nu : ((true , fp') ∷ Γ) ⊢ x ⊨' (fp' ⟮ args ⟯)

reference : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev : List (List (Set ℓ))} → (Γ : Context (Shape C) ℓ prev) → (x : Program C R) → (i : Fin (length prev)) → (args : Arguments ℓ (head (drop prev i))) → Set (s ⊔ p ⊔ r ⊔ sucˡ ℓ)
reference (_ ∷ Γ) x (suc i) args = reference Γ x i args
reference ((false , fp') ∷ Γ) x zero args = Mu Γ x fp' args
reference ((true , fp') ∷ Γ) x zero args = Nu Γ x fp' args

data _⊢_⊨'_ {C = C} {R = R} {ℓ = ℓ} where

  `true : ∀ {prev x} {Γ : Context (Shape C) ℓ prev}
      -------------
    → Γ ⊢ x ⊨' true

  `val : ∀ {prev x T} {Γ : Context (Shape C) ℓ prev}
    → T
      --------------
    → Γ ⊢ x ⊨' val T

  `lift : ∀ {prev x flag params f'} {Γ : Context (Shape C) ℓ prev} {fp' : FixedPoint' (Shape C) ℓ (params ∷ prev) params}
    → Γ ⊢ x ⊨' f'
      ---------------------------------
    → ((flag , fp') ∷ Γ) ⊢ x ⊨' lift f'

  _,_ : ∀ {prev x f'₁ f'₂} {Γ : Context (Shape C) ℓ prev}
    → Γ ⊢ x ⊨' f'₁
    → Γ ⊢ x ⊨' f'₂
      ------------------
    → Γ ⊢ x ⊨' f'₁ ∧ f'₂

  inj₁ : ∀ {prev x f'₁ f'₂} {Γ : Context (Shape C) ℓ prev}
    → Γ ⊢ x ⊨' f'₁
      ------------------
    → Γ ⊢ x ⊨' f'₁ ∨ f'₂

  inj₂ : ∀ {prev x f'₁ f'₂} {Γ : Context (Shape C) ℓ prev}
    → Γ ⊢ x ⊨' f'₂
      ------------------
    → Γ ⊢ x ⊨' f'₁ ∨ f'₂

  `∀ : ∀ {prev x T f'} {Γ : Context (Shape C) ℓ prev}
    → ((t : T) → Γ ⊢ x ⊨' f' t)
      ------------------
    → Γ ⊢ x ⊨' ∀⦗ T ⦘ f'

  `∃ : ∀ {prev x T f'} {Γ : Context (Shape C) ℓ prev}
    → (t : T)
    → Γ ⊢ x ⊨' f' t
      ------------------
    → Γ ⊢ x ⊨' ∃⦗ T ⦘ f'

  `⟨⟩-impure : ∀ {prev x af f'} {Γ : Context (Shape C) ℓ prev}
    → (s : Shape C)
    → (c : Position C s → Program C R)
    → free x ≡ impure (s , c)
    → s ∈ af
    → (p : Position C s)
    → Γ ⊢ c p ⊨' f'
      ------------------
    → Γ ⊢ x ⊨' ⟨ af ⟩ f'

  `[]-pure : ∀ {prev x af f'} {Γ : Context (Shape C) ℓ prev}
    → (r : R)
    → free x ≡ pure r
      ------------------
    → Γ ⊢ x ⊨' [ af ] f'

  `[]-impure : ∀ {prev x af f'} {Γ : Context (Shape C) ℓ prev}
    → (s : Shape C)
    → (c : Position C s → Program C R)
    → free x ≡ impure (s , c)
    → (s ∈ af → (p : Position C s) → Γ ⊢ c p ⊨' f')
      ------------------
    → Γ ⊢ x ⊨' [ af ] f'

  `μ : ∀ {prev x params⁺ fp'} {Γ : Context (Shape C) ℓ prev}
    → Mu Γ x fp' (get-args params⁺)
      -------------------------
    → Γ ⊢ x ⊨' μ params⁺ ． fp'

  `ν : ∀ {prev x params⁺ fp'} {Γ : Context (Shape C) ℓ prev}
    → Nu Γ x fp' (get-args params⁺)
      -------------------------
    → Γ ⊢ x ⊨' ν params⁺ ． fp'

  `ref : ∀ {prev x i args} {Γ : Context (Shape C) ℓ prev}
    → reference Γ x i args
      -----------------------
    → Γ ⊢ x ⊨' ref i ⦗ args ⦘

infix 25 _⊢_⊨ⁱ_

_⊢_⊨ⁱ_ : {C : Container s p} → {R : Set r} → {ℓ : Level} → {prev : List (List (Set ℓ))} → {flags : List Bool} → Context (Shape C) ℓ prev → Program C R → Formulaⁱ (Shape C) ℓ prev flags → Set (s ⊔ p ⊔ r ⊔ sucˡ ℓ)
Γ ⊢ x ⊨ⁱ fⁱ = Γ ⊢ x ⊨' fⁱ→f' fⁱ

infix 25 _⊨_

_⊨_ : {C : Container s p} → {R : Set r} → {ℓ : Level} → Program C R → Formula (Shape C) ℓ → Set (s ⊔ p ⊔ r ⊔ sucˡ ℓ)
x ⊨ f = [] ⊢ x ⊨ⁱ f
