{-# OPTIONS --without-K #-}
module ModalLogics.RegularFormulas.Base where

open import Common.Program using (Program; RecursiveProgram; recursionHandler)
open import Data.Bool using (Bool)
open import Data.Container using (Container; Shape)
open import Data.Container.FreeMonad using (_⋆_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (¬_; _because_; Dec)

open Bool
open Maybe
open IsDecEquivalence ⦃...⦄
open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

infix 60 not_
infixr 55 _∩_
infixr 55 _∪_

data ActionFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  act : Shape C → ActionFormula C
  all none : ActionFormula C
  not_ : ActionFormula C → ActionFormula C
  _∩_ _∪_ : ActionFormula C → ActionFormula C → ActionFormula C

infix 50 _*
infix 50 _⁺
infixr 45 _·_
infixr 45 _+_

data RegularFormula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  empty : RegularFormula C
  actF : ActionFormula C → RegularFormula C
  _·_ _+_ : RegularFormula C → RegularFormula C → RegularFormula C
  _* _⁺ : RegularFormula C → RegularFormula C

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_

data Formula (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula C
  ~_ : Formula C → Formula C
  _∧_ _∨_ _⇒_ : Formula C → Formula C → Formula C
  ⟨_⟩_ [_]_ : RegularFormula C → Formula C → Formula C

infix 25 _⊩_

_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formula C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂)
f ⊩ x = helper-dis (f''→fᵈⁿᶠ (f'→f'' (f→f' f))) x
  where
  parseActF : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → ActionFormula C → Shape C → Bool
  parseActF (act c₁) c₂ = ⌊ c₁ ≟ c₂ ⌋
  parseActF all _ = true
  parseActF none _ = false
  parseActF (not af) c = Data.Bool.not (parseActF af c)
  parseActF (af₁ ∩ af₂) c = Data.Bool._∧_ (parseActF af₁ c) (parseActF af₂ c)
  parseActF (af₁ ∪ af₂) c = Data.Bool._∨_ (parseActF af₁ c) (parseActF af₂ c)

  infix 50 _*'
  infixr 45 _·'_
  infixr 45 _+'_

  data RegularFormula' (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
    empty' : RegularFormula' C
    actF' : ActionFormula C → RegularFormula' C
    _·'_ _+'_ : RegularFormula' C → RegularFormula' C → RegularFormula' C
    _*' : RegularFormula' C → RegularFormula' C

  rf→rf' : {C : Container ℓ₁ ℓ₂} → RegularFormula C → RegularFormula' C
  rf→rf' empty = empty'
  rf→rf' (actF af) = actF' af
  rf→rf' (rf₁ · rf₂) = rf→rf' rf₁ ·' rf→rf' rf₂
  rf→rf' (rf₁ + rf₂) = rf→rf' rf₁ +' rf→rf' rf₂
  rf→rf' (rf *) = rf→rf' rf *'
  rf→rf' (rf ⁺) = rf' ·' rf' *'
    where
    rf' = rf→rf' rf

  data RegularFormulaᵈⁿᶠ-var (C : Container ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ-con (C : Container ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ-dis (C : Container ℓ₁ ℓ₂) : Set ℓ₁

  data RegularFormulaᵈⁿᶠ-var C where
    var-empty : RegularFormulaᵈⁿᶠ-var C
    var-af : ActionFormula C → RegularFormulaᵈⁿᶠ-var C
    var-* : RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-var C

  data RegularFormulaᵈⁿᶠ-con C where
    con-var : RegularFormulaᵈⁿᶠ-var C → RegularFormulaᵈⁿᶠ-con C
    con-and : RegularFormulaᵈⁿᶠ-var C → RegularFormulaᵈⁿᶠ-con C → RegularFormulaᵈⁿᶠ-con C

  data RegularFormulaᵈⁿᶠ-dis C where
    dis-con : RegularFormulaᵈⁿᶠ-con C → RegularFormulaᵈⁿᶠ-dis C
    dis-or : RegularFormulaᵈⁿᶠ-con C → RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-dis C

  rf-merge-con : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-con C → RegularFormulaᵈⁿᶠ-con C → RegularFormulaᵈⁿᶠ-con C
  rf-merge-con (con-var var) con = con-and var con
  rf-merge-con (con-and var con₁) con₂ = con-and var (rf-merge-con con₁ con₂)

  rf-merge-dis-or : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-dis C
  rf-merge-dis-or (dis-con con) dis = dis-or con dis
  rf-merge-dis-or (dis-or con dis₁) dis₂ = dis-or con (rf-merge-dis-or dis₁ dis₂)

  rf-helper : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-con C → RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-dis C
  rf-helper con₁ (dis-con con₂) = dis-con (rf-merge-con con₁ con₂)
  rf-helper con₁ (dis-or con₂ dis) = dis-or (rf-merge-con con₁ con₂) (rf-helper con₁ dis)

  rf-merge-dis-and : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-dis C → RegularFormulaᵈⁿᶠ-dis C
  rf-merge-dis-and (dis-con con) dis = rf-helper con dis
  rf-merge-dis-and (dis-or con dis₁) dis₂ = rf-merge-dis-or (rf-helper con dis₂) (rf-merge-dis-and dis₁ dis₂)

  rf'→dis : {C : Container ℓ₁ ℓ₂} → RegularFormula' C → RegularFormulaᵈⁿᶠ-dis C
  rf'→dis empty' = dis-con (con-var var-empty)
  rf'→dis (actF' af) = dis-con (con-var (var-af af))
  rf'→dis (rf'₁ ·' rf'₂) = rf-merge-dis-and (rf'→dis rf'₁) (rf'→dis rf'₂)
  rf'→dis (rf'₁ +' rf'₂) = rf-merge-dis-or (rf'→dis rf'₁) (rf'→dis rf'₂)
  rf'→dis (rf' *') = dis-con (con-var (var-* (rf'→dis rf')))

  data RegularFormulaᵈⁿᶠ'-var (C : Container ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ'-con (C : Container ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ'-dis (C : Container ℓ₁ ℓ₂) : Set ℓ₁

  data RegularFormulaᵈⁿᶠ'-var C where
    var'-af : ActionFormula C → RegularFormulaᵈⁿᶠ'-var C
    var'-* : RegularFormulaᵈⁿᶠ'-dis C → RegularFormulaᵈⁿᶠ'-var C

  data RegularFormulaᵈⁿᶠ'-con C where
    con'-var' : RegularFormulaᵈⁿᶠ'-var C → RegularFormulaᵈⁿᶠ'-con C
    con'-and : RegularFormulaᵈⁿᶠ'-var C → RegularFormulaᵈⁿᶠ'-con C → RegularFormulaᵈⁿᶠ'-con C

  data RegularFormulaᵈⁿᶠ'-dis C where
    dis'-con' : RegularFormulaᵈⁿᶠ'-con C → RegularFormulaᵈⁿᶠ'-dis C
    dis'-or : RegularFormulaᵈⁿᶠ'-con C → RegularFormulaᵈⁿᶠ'-dis C → RegularFormulaᵈⁿᶠ'-dis C

  var→var' : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-var C → Maybe (RegularFormulaᵈⁿᶠ'-var C)
  con→con' : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-con C → Maybe (RegularFormulaᵈⁿᶠ'-con C)
  dis→dis' : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ-dis C → Maybe (RegularFormulaᵈⁿᶠ'-dis C)

  var→var' var-empty = nothing
  var→var' (var-af af) = just (var'-af af)
  var→var' (var-* dis) with dis→dis' dis
  ... | just dis' = just (var'-* dis')
  ... | nothing = nothing

  con→con' (con-var var) with var→var' var
  ... | just var' = just (con'-var' var')
  ... | nothing = nothing
  con→con' (con-and var con) with var→var' var | con→con' con
  ... | just var' | just con' = just (con'-and var' con')
  ... | just var' | nothing = just (con'-var' var')
  ... | nothing | con' = con'

  dis→dis' (dis-con con) with con→con' con
  ... | just con' = just (dis'-con' con')
  ... | nothing = nothing
  dis→dis' (dis-or con dis) with con→con' con | dis→dis' dis
  ... | just con' | just dis' = just (dis'-or con' dis')
  ... | just con' | nothing = just (dis'-con' con')
  ... | nothing | dis' = dis'

  infix 40 ~'_
  infixr 35 _∧'_
  infixr 35 _∨'_
  infix 30 ⟨_⟩'_
  infix 30 [_]'_

  data Formula' (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
    true' false' : Formula' C
    ~'_ : Formula' C → Formula' C
    _∧'_ _∨'_ : Formula' C → Formula' C → Formula' C
    ⟨_⟩'_ [_]'_ : RegularFormulaᵈⁿᶠ'-dis C → Formula' C → Formula' C

  f→f' : {C : Container ℓ₁ ℓ₂} → Formula C → Formula' C
  f→f' true = true'
  f→f' false = false'
  f→f' (~ f) = ~' f→f' f
  f→f' (f₁ ∧ f₂) = f→f' f₁ ∧' f→f' f₂
  f→f' (f₁ ∨ f₂) = f→f' f₁ ∨' f→f' f₂
  f→f' (f₁ ⇒ f₂) = (~' f→f' f₁) ∨' f→f' f₂
  f→f' (⟨ rf ⟩ f) with dis→dis' (rf'→dis (rf→rf' rf))
  ... | just dis = ⟨ dis ⟩' f→f' f
  ... | nothing = f→f' f
  f→f' ([ rf ] f) with dis→dis' (rf'→dis (rf→rf' rf))
  ... | just dis = [ dis ]' f→f' f
  ... | nothing = f→f' f

  infixr 35 _∧''_
  infixr 35 _∨''_
  infix 30 ⟨_⟩''_
  infix 30 [_]''_

  data Formula'' (C : Container ℓ₁ ℓ₂) : Set ℓ₁ where
    true'' false'' : Formula'' C
    _∧''_ _∨''_ : Formula'' C → Formula'' C → Formula'' C
    ⟨_⟩''_ [_]''_ : RegularFormulaᵈⁿᶠ'-dis C → Formula'' C → Formula'' C

  f'→f'' : {C : Container ℓ₁ ℓ₂} → Formula' C → Formula'' C
  f'→f'' true' = true''
  f'→f'' false' = false''
  f'→f'' (~' f') = negate f'
    where
    negate : {C : Container ℓ₁ ℓ₂} → Formula' C → Formula'' C
    negate true' = false''
    negate false' = true''
    negate (~' f') = negate f'
    negate (f'₁ ∧' f'₂) = negate f'₁ ∨'' negate f'₂
    negate (f'₁ ∨' f'₂) = negate f'₁ ∧'' negate f'₂
    negate (⟨ dis' ⟩' f') = [ dis' ]'' negate f'
    negate ([ dis' ]' f') = ⟨ dis' ⟩'' negate f'
  f'→f'' (f'₁ ∧' f'₂) = f'→f'' f'₁ ∧'' f'→f'' f'₂
  f'→f'' (f'₁ ∨' f'₂) = f'→f'' f'₁ ∨'' f'→f'' f'₂
  f'→f'' (⟨ dis' ⟩' f') = ⟨ dis' ⟩'' f'→f'' f'
  f'→f'' ([ dis' ]' f') = [ dis' ]'' f'→f'' f'

  data Formulaᵈⁿᶠ-var (C : Container ℓ₁ ℓ₂) : Set ℓ₁
  data Formulaᵈⁿᶠ-con (C : Container ℓ₁ ℓ₂) : Set ℓ₁
  data Formulaᵈⁿᶠ-dis (C : Container ℓ₁ ℓ₂) : Set ℓ₁

  data Formulaᵈⁿᶠ-var C where
    trueᵈⁿᶠ falseᵈⁿᶠ : Formulaᵈⁿᶠ-var C
    ⟨_⟩ᵈⁿᶠ [_]ᵈⁿᶠ : RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-var C → Formulaᵈⁿᶠ-var C

  data Formulaᵈⁿᶠ-con C where
    f-var : Formulaᵈⁿᶠ-var C → Formulaᵈⁿᶠ-con C
    _∧ᵈⁿᶠ_ : Formulaᵈⁿᶠ-var C → Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-con C

  data Formulaᵈⁿᶠ-dis C where
    f-con : Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-dis C
    _∨ᵈⁿᶠ_ : Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C

  f-merge-con : {C : Container ℓ₁ ℓ₂} → Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-con C
  f-merge-con (f-var var) con = var ∧ᵈⁿᶠ con
  f-merge-con (var ∧ᵈⁿᶠ con₁) con₂ = var ∧ᵈⁿᶠ f-merge-con con₁ con₂

  f-merge-dis-or : {C : Container ℓ₁ ℓ₂} → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C
  f-merge-dis-or (f-con con) dis = con ∨ᵈⁿᶠ dis
  f-merge-dis-or (con ∨ᵈⁿᶠ dis₁) dis₂ = con ∨ᵈⁿᶠ f-merge-dis-or dis₁ dis₂

  f-helper : {C : Container ℓ₁ ℓ₂} → Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C
  f-helper con₁ (f-con con₂) = f-con (f-merge-con con₁ con₂)
  f-helper con₁ (con₂ ∨ᵈⁿᶠ dis₂) = f-merge-con con₁ con₂ ∨ᵈⁿᶠ f-helper con₁ dis₂

  f-merge-dis-and : {C : Container ℓ₁ ℓ₂} → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C
  f-merge-dis-and (f-con con) dis = f-helper con dis
  f-merge-dis-and (con ∨ᵈⁿᶠ dis₁) dis₂ = f-merge-dis-or (f-helper con dis₂) (f-merge-dis-and dis₁ dis₂)

  f''→fᵈⁿᶠ : {C : Container ℓ₁ ℓ₂} → Formula'' C → Formulaᵈⁿᶠ-dis C
  f''→fᵈⁿᶠ true'' = f-con (f-var trueᵈⁿᶠ)
  f''→fᵈⁿᶠ false'' = f-con (f-var falseᵈⁿᶠ)
  f''→fᵈⁿᶠ (f''₁ ∧'' f''₂) = f-merge-dis-and (f''→fᵈⁿᶠ f''₁) (f''→fᵈⁿᶠ f''₂)
  f''→fᵈⁿᶠ (f''₁ ∨'' f''₂) = f-merge-dis-or (f''→fᵈⁿᶠ f''₁) (f''→fᵈⁿᶠ f''₂)
  f''→fᵈⁿᶠ (⟨ rf ⟩'' f'') = merge-∃-dis rf (f''→fᵈⁿᶠ f'')
    where
    merge-∃-var : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-var C → Formulaᵈⁿᶠ-var C
    merge-∃-var rf var = ⟨ rf ⟩ᵈⁿᶠ var

    merge-∃-con : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-con C
    merge-∃-con rf (f-var var) = f-var (merge-∃-var rf var)
    merge-∃-con rf (var ∧ᵈⁿᶠ con) = merge-∃-var rf var ∧ᵈⁿᶠ merge-∃-con rf con

    merge-∃-dis : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C
    merge-∃-dis rf (f-con con) = f-con (merge-∃-con rf con)
    merge-∃-dis rf (con ∨ᵈⁿᶠ dis) = merge-∃-con rf con ∨ᵈⁿᶠ merge-∃-dis rf dis
  f''→fᵈⁿᶠ ([ rf ]'' f'') = merge-∀-dis rf (f''→fᵈⁿᶠ f'')
    where
    merge-∀-var : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-var C → Formulaᵈⁿᶠ-var C
    merge-∀-var rf var = [ rf ]ᵈⁿᶠ var

    merge-∀-con : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-con C → Formulaᵈⁿᶠ-con C
    merge-∀-con rf (f-var var) = f-var (merge-∀-var rf var)
    merge-∀-con rf (var ∧ᵈⁿᶠ con) = merge-∀-var rf var ∧ᵈⁿᶠ merge-∀-con rf con

    merge-∀-dis : {C : Container ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis C → Formulaᵈⁿᶠ-dis C → Formulaᵈⁿᶠ-dis C
    merge-∀-dis rf (f-con con) = f-con (merge-∀-con rf con)
    merge-∀-dis rf (con ∨ᵈⁿᶠ dis) = merge-∀-con rf con ∨ᵈⁿᶠ merge-∀-dis rf dis

  helper-var : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-var C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂)
  helper-var trueᵈⁿᶠ _ = ⊤
  helper-var falseᵈⁿᶠ _ = ⊥
  helper-var (⟨ dis' ⟩ᵈⁿᶠ var) x = {!   !}
  helper-var ([ dis' ]ᵈⁿᶠ var) x = {!   !}

  helper-con : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-con C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂)
  helper-con (f-var var) x = helper-var var x
  helper-con (var ∧ᵈⁿᶠ con) x = helper-var var x × helper-con con x

  helper-dis : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ-dis C → C ⋆ α → Set (ℓ₁ ⊔ ℓ₂)
  helper-dis (f-con con) x = helper-con con x
  helper-dis (con ∨ᵈⁿᶠ dis) x = helper-con con x ⊎ helper-dis dis x

postulate
  ⊩-dec : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {α : Set ℓ₃} → (f : Formula C) → (x : C ⋆ α) → Dec (f ⊩ x)

infix 25 _!_⊩_

_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → I → Formula C → Program C I O → Set (ℓ₁ ⊔ ℓ₂)
i ! f ⊩ x = f ⊩ (x i)

⊩-decP : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → (f : Formula C) → (x : Program C I O) → Dec (i ! f ⊩ x)
does ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decP i f x ⦄ with ⊩-dec f (x i)
... | _ because proof = proof

infix 25 _▸_!_⊩_

_▸_!_⊩_ : {C : Container ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → I → Formula C → RecursiveProgram C I O → Set (ℓ₁ ⊔ ℓ₂)
n ▸ i ! f ⊩ x = f ⊩ (recursionHandler x n) i

⊩-decR : {C : Container ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = Shape C} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (i : I) → (f : Formula C) → (x : RecursiveProgram C I O) → Dec (n ▸ i ! f ⊩ x)
does ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | does because _ = does
proof ⦃ ⊩-decR n i f x ⦄ with ⊩-dec f ((recursionHandler x n) i)
... | _ because proof = proof
