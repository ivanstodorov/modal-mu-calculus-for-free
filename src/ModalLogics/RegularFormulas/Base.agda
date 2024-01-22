module ModalLogics.RegularFormulas.Base where

open import Common.Effect
open import Common.Free
open import Common.Program
open import Data.Bool using (Bool; true; false)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Nullary using (¬_; _because_; Dec)

open Effect
open Dec ⦃...⦄
open IsDecEquivalence ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data ActionFormula (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁ where
  act : C ε → ActionFormula ε
  all none : ActionFormula ε
  not_ : ActionFormula ε → ActionFormula ε
  _∩_ _∪_ : ActionFormula ε → ActionFormula ε → ActionFormula ε

infix 60 not_
infixr 55 _∩_
infixr 55 _∪_

data RegularFormula (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁ where
  empty : RegularFormula ε
  actF : ActionFormula ε → RegularFormula ε
  _·_ _+_ : RegularFormula ε → RegularFormula ε → RegularFormula ε
  _* _⁺ : RegularFormula ε → RegularFormula ε

infix 50 _*
infix 50 _⁺
infixr 45 _·_
infixr 45 _+_

data Formula (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁ where
  true false : Formula ε
  ~_ : Formula ε → Formula ε
  _∧_ _∨_ _⇒_ : Formula ε → Formula ε → Formula ε
  ⟨_⟩_ [_]_ : RegularFormula ε → Formula ε → Formula ε

infix 40 ~_
infixr 35 _∧_
infixr 35 _∨_
infixr 35 _⇒_
infix 30 ⟨_⟩_
infix 30 [_]_

_⊢_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → Formula ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
f ⊢ x = f→fᵈⁿᶠ f ⊢ᵈⁿᶠ x
  where
  parseActF : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → ActionFormula ε → C ε → Bool
  parseActF (act c₁) c₂ = ⌊ c₁ ≟ c₂ ⌋
  parseActF all _ = true
  parseActF none _ = false
  parseActF (not af) c = Data.Bool.not (parseActF af c)
  parseActF (af₁ ∩ af₂) c = Data.Bool._∧_ (parseActF af₁ c) (parseActF af₂ c)
  parseActF (af₁ ∪ af₂) c = Data.Bool._∨_ (parseActF af₁ c) (parseActF af₂ c)

  data RegularFormula' (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁ where
    empty' : RegularFormula' ε
    actF' : ActionFormula ε → RegularFormula' ε
    _·'_ _+'_ : RegularFormula' ε → RegularFormula' ε → RegularFormula' ε
    _*' : RegularFormula' ε → RegularFormula' ε

  infix 50 _*'
  infixr 45 _·'_
  infixr 45 _+'_

  rf→rf' : {ε : Effect ℓ₁ ℓ₂} → RegularFormula ε → RegularFormula' ε
  rf→rf' empty = empty'
  rf→rf' (actF af) = actF' af
  rf→rf' (rf₁ · rf₂) = rf→rf' rf₁ ·' rf→rf' rf₂
  rf→rf' (rf₁ + rf₂) = rf→rf' rf₁ +' rf→rf' rf₂
  rf→rf' (rf *) = rf→rf' rf *'
  rf→rf' (rf ⁺) = rf' ·' rf' *'
    where
    rf' = rf→rf' rf

  data RegularFormulaᵈⁿᶠ'-var (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ'-con (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ'-dis (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁

  data RegularFormulaᵈⁿᶠ'-var ε where
    var'-empty : RegularFormulaᵈⁿᶠ'-var ε
    var'-af : ActionFormula ε → RegularFormulaᵈⁿᶠ'-var ε
    var'-* : RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-var ε

  data RegularFormulaᵈⁿᶠ'-con ε where
    con'-var : RegularFormulaᵈⁿᶠ'-var ε → RegularFormulaᵈⁿᶠ'-con ε
    con'-and : RegularFormulaᵈⁿᶠ'-var ε → RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ'-con ε

  data RegularFormulaᵈⁿᶠ'-dis ε where
    dis'-con : RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ'-dis ε
    dis'-or : RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-dis ε

  merge-con' : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ'-con ε
  merge-con' (con'-var var) con = con'-and var con
  merge-con' (con'-and var con₁) con₂ = con'-and var (merge-con' con₁ con₂)

  merge-dis'-or : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-dis ε
  merge-dis'-or (dis'-con con) dis = dis'-or con dis
  merge-dis'-or (dis'-or con dis₁) dis₂ = dis'-or con (merge-dis'-or dis₁ dis₂)

  helper : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-dis ε
  helper con₁ (dis'-con con₂) = dis'-con (merge-con' con₁ con₂)
  helper con₁ (dis'-or con₂ dis) = dis'-or (merge-con' con₁ con₂) (helper con₁ dis)

  merge-dis'-and : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ'-dis ε
  merge-dis'-and (dis'-con con) dis = helper con dis
  merge-dis'-and (dis'-or con dis₁) dis₂ = merge-dis'-or (helper con dis₂) (merge-dis'-and dis₁ dis₂)

  rf'→dis' : {ε : Effect ℓ₁ ℓ₂} → RegularFormula' ε → RegularFormulaᵈⁿᶠ'-dis ε
  rf'→dis' empty' = dis'-con (con'-var var'-empty)
  rf'→dis' (actF' af) = dis'-con (con'-var (var'-af af))
  rf'→dis' (rf'₁ ·' rf'₂) with rf'→dis' rf'₁ | rf'→dis' rf'₂
  ... | dis₁ | dis₂ = merge-dis'-and dis₁ dis₂
  rf'→dis' (rf'₁ +' rf'₂) with rf'→dis' rf'₁ | rf'→dis' rf'₂
  ... | dis₁ | dis₂ = merge-dis'-or dis₁ dis₂
  rf'→dis' (rf' *') = dis'-con (con'-var (var'-* (rf'→dis' rf')))

  data RegularFormulaᵈⁿᶠ-var (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ-con (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁
  data RegularFormulaᵈⁿᶠ-dis (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁

  data RegularFormulaᵈⁿᶠ-var ε where
    var-af : ActionFormula ε → RegularFormulaᵈⁿᶠ-var ε
    var-* : RegularFormulaᵈⁿᶠ-dis ε → RegularFormulaᵈⁿᶠ-var ε

  data RegularFormulaᵈⁿᶠ-con ε where
    con-var : RegularFormulaᵈⁿᶠ-var ε → RegularFormulaᵈⁿᶠ-con ε
    con-and : RegularFormulaᵈⁿᶠ-var ε → RegularFormulaᵈⁿᶠ-con ε → RegularFormulaᵈⁿᶠ-con ε

  data RegularFormulaᵈⁿᶠ-dis ε where
    dis-con : RegularFormulaᵈⁿᶠ-con ε → RegularFormulaᵈⁿᶠ-dis ε
    dis-or : RegularFormulaᵈⁿᶠ-con ε → RegularFormulaᵈⁿᶠ-dis ε → RegularFormulaᵈⁿᶠ-dis ε

  var'→var : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-var ε → RegularFormulaᵈⁿᶠ-var ε ⊎ ⊤₀
  con'→con : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-con ε → RegularFormulaᵈⁿᶠ-con ε ⊎ ⊤₀
  dis'→dis : {ε : Effect ℓ₁ ℓ₂} → RegularFormulaᵈⁿᶠ'-dis ε → RegularFormulaᵈⁿᶠ-dis ε ⊎ ⊤₀

  var'→var var'-empty = inj₂ tt₀
  var'→var (var'-af af) = inj₁ (var-af af)
  var'→var (var'-* dis') with dis'→dis dis'
  ... | inj₁ dis = inj₁ (var-* dis)
  ... | inj₂ _ = inj₂ tt₀

  con'→con (con'-var var') with var'→var var'
  ... | inj₁ var = inj₁ (con-var var)
  ... | inj₂ _ = inj₂ tt₀
  con'→con (con'-and var' con') with var'→var var' | con'→con con'
  ... | inj₁ var | inj₁ con = inj₁ (con-and var con)
  ... | inj₁ var | inj₂ _ = inj₁ (con-var var)
  ... | inj₂ _ | con = con

  dis'→dis (dis'-con con') with con'→con con'
  ... | inj₁ con = inj₁ (dis-con con)
  ... | inj₂ _ = inj₂ tt₀
  dis'→dis (dis'-or con' dis') with con'→con con' | dis'→dis dis'
  ... | inj₁ con | inj₁ dis = inj₁ (dis-or con dis)
  ... | inj₁ con | inj₂ _ = inj₁ (dis-con con)
  ... | inj₂ _ | dis = dis

  data Formulaᵈⁿᶠ (ε : Effect ℓ₁ ℓ₂) : Set ℓ₁ where
    trueᵈⁿᶠ falseᵈⁿᶠ : Formulaᵈⁿᶠ ε
    ~ᵈⁿᶠ_ : Formulaᵈⁿᶠ ε → Formulaᵈⁿᶠ ε
    _∧ᵈⁿᶠ_ _∨ᵈⁿᶠ_ : Formulaᵈⁿᶠ ε → Formulaᵈⁿᶠ ε → Formulaᵈⁿᶠ ε
    ⟨_⟩ᵈⁿᶠ_ [_]ᵈⁿᶠ_ : RegularFormulaᵈⁿᶠ-dis ε → Formulaᵈⁿᶠ ε → Formulaᵈⁿᶠ ε

  infix 40 ~ᵈⁿᶠ_
  infixr 35 _∧ᵈⁿᶠ_
  infixr 35 _∨ᵈⁿᶠ_
  infix 30 ⟨_⟩ᵈⁿᶠ_
  infix 30 [_]ᵈⁿᶠ_

  f→fᵈⁿᶠ : {ε : Effect ℓ₁ ℓ₂} → Formula ε → Formulaᵈⁿᶠ ε
  f→fᵈⁿᶠ true = trueᵈⁿᶠ
  f→fᵈⁿᶠ false = falseᵈⁿᶠ
  f→fᵈⁿᶠ (~ f) = ~ᵈⁿᶠ f→fᵈⁿᶠ f
  f→fᵈⁿᶠ (f₁ ∧ f₂) = f→fᵈⁿᶠ f₁ ∧ᵈⁿᶠ f→fᵈⁿᶠ f₂
  f→fᵈⁿᶠ (f₁ ∨ f₂) = f→fᵈⁿᶠ f₁ ∨ᵈⁿᶠ f→fᵈⁿᶠ f₂
  f→fᵈⁿᶠ (f₁ ⇒ f₂) = (~ᵈⁿᶠ f→fᵈⁿᶠ f₁) ∨ᵈⁿᶠ f→fᵈⁿᶠ f₂
  f→fᵈⁿᶠ (⟨ rf ⟩ f) with dis'→dis (rf'→dis' (rf→rf' rf))
  ... | inj₁ dis = ⟨ dis ⟩ᵈⁿᶠ f→fᵈⁿᶠ f
  ... | inj₂ _ = f→fᵈⁿᶠ f
  f→fᵈⁿᶠ ([ rf ] f) with dis'→dis (rf'→dis' (rf→rf' rf))
  ... | inj₁ dis = [ dis ]ᵈⁿᶠ f→fᵈⁿᶠ f
  ... | inj₂ _ = f→fᵈⁿᶠ f

  _⊢ᵈⁿᶠ_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
  helper-∃-var : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → RegularFormulaᵈⁿᶠ-var ε → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
  helper-∃-con : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → RegularFormulaᵈⁿᶠ-con ε → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
  helper-∃-dis : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → RegularFormulaᵈⁿᶠ-dis ε → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
  helper-∀-var : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → RegularFormulaᵈⁿᶠ-var ε → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
  helper-∀-con : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → RegularFormulaᵈⁿᶠ-con ε → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)
  helper-∀-dis : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → RegularFormulaᵈⁿᶠ-dis ε → Formulaᵈⁿᶠ ε → Free ε α → Set (ℓ₁ ⊔ ℓ₂)

  helper-∃-var (var-af _) _ (pure _) = ⊥
  helper-∃-var (var-af af) fᵈⁿᶠ (step c k) with parseActF af c
  ... | false = ⊥
  ... | true = ∃[ r ] fᵈⁿᶠ ⊢ᵈⁿᶠ k r
  helper-∃-var (var-* dis) fᵈⁿᶠ x = {!   !} -- fᵈⁿᶠ ⊢ᵈⁿᶠ x ⊎ helper-∃-dis dis (⟨ dis-con (con-var (var-* dis)) ⟩ᵈⁿᶠ fᵈⁿᶠ) x

  helper-∃-con (con-var var) fᵈⁿᶠ x = helper-∃-var var fᵈⁿᶠ x
  helper-∃-con (con-and var con) fᵈⁿᶠ x = helper-∃-var var fᵈⁿᶠ x × helper-∃-con con fᵈⁿᶠ x

  helper-∃-dis (dis-con con) fᵈⁿᶠ x = helper-∃-con con fᵈⁿᶠ x
  helper-∃-dis (dis-or con dis) fᵈⁿᶠ x = helper-∃-con con fᵈⁿᶠ x ⊎ helper-∃-dis dis fᵈⁿᶠ x

  helper-∀-var (var-af _) _ (pure _) = ⊤
  helper-∀-var (var-af af) fᵈⁿᶠ (step c k) with parseActF af c
  ... | false = ⊤
  ... | true = ∀ r → fᵈⁿᶠ ⊢ᵈⁿᶠ k r
  helper-∀-var (var-* dis) fᵈⁿᶠ x = {!   !} -- fᵈⁿᶠ ⊢ᵈⁿᶠ x ⊎ helper-∀-dis dis ([ dis-con (con-var (var-* dis)) ]ᵈⁿᶠ fᵈⁿᶠ) x

  helper-∀-con (con-var var) fᵈⁿᶠ x = helper-∀-var var fᵈⁿᶠ x
  helper-∀-con (con-and var con) fᵈⁿᶠ x = helper-∀-var var fᵈⁿᶠ x × helper-∀-con con fᵈⁿᶠ x

  helper-∀-dis (dis-con con) fᵈⁿᶠ x = helper-∀-con con fᵈⁿᶠ x
  helper-∀-dis (dis-or con dis) fᵈⁿᶠ x = helper-∀-con con fᵈⁿᶠ x ⊎ helper-∀-dis dis fᵈⁿᶠ x

  trueᵈⁿᶠ ⊢ᵈⁿᶠ _ = ⊤
  falseᵈⁿᶠ ⊢ᵈⁿᶠ _ = ⊥
  (~ᵈⁿᶠ fᵈⁿᶠ) ⊢ᵈⁿᶠ x = ¬ fᵈⁿᶠ ⊢ᵈⁿᶠ x
  (fᵈⁿᶠ₁ ∧ᵈⁿᶠ fᵈⁿᶠ₂) ⊢ᵈⁿᶠ x = fᵈⁿᶠ₁ ⊢ᵈⁿᶠ x × fᵈⁿᶠ₂ ⊢ᵈⁿᶠ x
  (fᵈⁿᶠ₁ ∨ᵈⁿᶠ fᵈⁿᶠ₂) ⊢ᵈⁿᶠ x = fᵈⁿᶠ₁ ⊢ᵈⁿᶠ x ⊎ fᵈⁿᶠ₂ ⊢ᵈⁿᶠ x
  (⟨ dis ⟩ᵈⁿᶠ fᵈⁿᶠ) ⊢ᵈⁿᶠ x = helper-∃-dis dis fᵈⁿᶠ x
  ([ dis ]ᵈⁿᶠ fᵈⁿᶠ) ⊢ᵈⁿᶠ x = helper-∀-dis dis fᵈⁿᶠ x

infix 25 _⊢_

postulate
  ⊢-dec : {ε : Effect ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = C ε} _≡_ ⦄ → {α : Set ℓ₃} → (f : Formula ε) → (x : Free ε α) → Dec (f ⊢ x)

_⊢_!_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → Formula ε → program ε I O → I → Set (ℓ₁ ⊔ ℓ₂)
f ⊢ x ! i = f ⊢ (x i)

infix 25 _⊢_!_

⊢-decP : {ε : Effect ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula ε) → (x : program ε I O) → (i : I) → Dec (f ⊢ x ! i)
does ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | does₁ because _ = does₁
proof ⦃ ⊢-decP f x i ⦄ with ⊢-dec f (x i)
... | _ because proof₁ = proof₁

_▸_⊢_!_ : {ε : Effect ℓ₁ ℓ₂} → ⦃ IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → ℕ → Formula ε → recursiveProgram ε I O → I → Set (ℓ₁ ⊔ ℓ₂)
n ▸ f ⊢ x ! i = f ⊢ (recursionHandler x n) i

infix 25 _▸_⊢_!_
 
⊢-decR : {ε : Effect ℓ₁ ℓ₂} → ⦃ _ : IsDecEquivalence {A = C ε} _≡_ ⦄ → {I : Set ℓ₃} → {O : I → Set ℓ₄} → (n : ℕ) → (f : Formula ε) → (x : recursiveProgram ε I O) → (i : I) → Dec (n ▸ f ⊢ x ! i)
does ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | does₁ because _ = does₁
proof ⦃ ⊢-decR n f x i ⦄ with ⊢-dec f ((recursionHandler x n) i)
... | _ because proof₁ = proof₁
