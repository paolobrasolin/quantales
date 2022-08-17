{-# OPTIONS --without-K #-}

module Quantale where

open import Algebra.Lattice.Bundles

open import Algebra.Core
open import Algebra.Structures
open import Level using (Level; suc; _⊔_)
open import Relation.Binary
open import Data.Empty.Polymorphic
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; subst₂)

record hasSups c ℓ (I : Set (c ⊔ ℓ)) (P : Set c) (_≤_ : Rel P ℓ) (f : I → P) : (Set (suc (c ⊔ ℓ))) where
  field
    s : P
    isUB : ∀ (i : I) → (f i) ≤ s
    isLUB : (t : P) → (∀ (i : I) → f i ≤ t) → s ≤ t

record IsCompleteJSL {c ℓ ℓ'} {A : Set c} (_≈_ : Rel A ℓ) (_≤_ : Rel A ℓ') : Set (suc (c ⊔ ℓ ⊔ ℓ')) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    sups : ∀ {I : Set (c ⊔ ℓ')} {f : I → A} → hasSups c ℓ' I A (_≤_) f
  open IsPartialOrder isPartialOrder public

record CompleteJSL c ℓ ℓ' : Set (suc (c ⊔ ℓ ⊔ ℓ')) where
  infix  4 _≈_ _≤_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _≤_           : Rel Carrier ℓ'
    isCompleteJSL : IsCompleteJSL _≈_ _≤_
  open IsCompleteJSL isCompleteJSL public

record Quantale c ℓ ℓ' : Set (suc (c ⊔ ℓ ⊔ ℓ')) where
  infix 4 _≈_ _≤_
  infix 5 _*_
  field
    -- order structure
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _≤_           : Rel Carrier ℓ'
    isCompleteJSL : IsCompleteJSL _≈_ _≤_
    -- semigroup structure
    _*_           : Op₂ Carrier
    isSemigroup   : IsSemigroup _≈_ _*_
  open IsCompleteJSL isCompleteJSL public hiding (refl; reflexive; isEquivalence) -- TODO: evitare questo
  field
    distrˡ        : (I : Set (c ⊔ ℓ')) (y : I → Carrier) (x : Carrier) → (x * hasSups.s (sups {I} {y})) ≈ hasSups.s (sups {I} {λ i → x * (y i)})
    distrʳ        : (I : Set (c ⊔ ℓ')) (y : I → Carrier) (x : Carrier) → (hasSups.s (sups {I} {y})) * x ≈ hasSups.s (sups {I} {λ i → (y i) * x})
  open IsSemigroup isSemigroup public

module Minima {c a b} (Q : Quantale c a b) where

  open module zap = Quantale Q
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Agda.Builtin.Sigma

  postulate
    ⊥-initial : {A : Set c} {f : (⊥ {c ⊔ b}) → A} → f ≡ ⊥-elim

  subst : ∀ {A : Set c} (_∼_ : Rel A a) {x y} → (eq : IsEquivalence _∼_) → x ≡ y → x ∼ y
  subst _∼_ record { refl = refl ; sym = _ ; trans = _ } p rewrite p = refl

  record min : Set (suc (c ⊔ a ⊔ b)) where
    field
      bot : Carrier
      isMin : ∀ {t : Carrier} → bot ≤ t

  has⊥ : min
  has⊥ = record
    { bot = hasSups.s emptyFamily
    ; isMin = λ {t} → hasSups.isLUB emptyFamily t ⊥-elim
    }
    where
      emptyFamily : _
      emptyFamily = (IsCompleteJSL.sups isCompleteJSL) {⊥} {⊥-elim}

  ⊥-absorbsˡ : ∀ (x : Carrier) → x * (min.bot has⊥) ≈ (min.bot has⊥)
  ⊥-absorbsˡ x = begin x * min.bot has⊥                            ≈⟨ distrˡ ⊥ ⊥-elim x ⟩
                       hasSups.s (sups {⊥} {λ i → x * (⊥-elim i)}) ≈⟨ subst _≈_ isEquivalence (Eq.cong (λ t → hasSups.s (sups {⊥} {t})) ⊥-initial) ⟩
                       hasSups.s (sups {⊥} {⊥-elim})               ≈⟨ subst _≈_ isEquivalence _≡_.refl ⟩
                       min.bot has⊥                                ∎

open Minima

module Exponentials {c a b} (Q : Quantale c a b) where

  open module zop = Quantale Q

  open import Agda.Builtin.Sigma

  _⇀_ : (p : Carrier) → (q : Carrier) → hasSups c b (Σ Carrier (λ x → p * x ≤ q)) Carrier _≤_ (λ ( x , _ ) → x)
  p ⇀ q = sups {Σ Carrier (λ x → p * x ≤ q)} {λ {(x , _ ) → x}}

  -- adjunction properties
  adjunctionTo : {x y z : Carrier} → y * x ≤ z → x ≤ hasSups.s (y ⇀ z)
  adjunctionTo {x} {y} {z} y*x≤z = hasSups.isUB yoink ( x , y*x≤z)
   where yoink = sups {Σ Carrier (λ x → y * x ≤ z)} {λ {(x , _ ) → x}}

  adjunctionFrom : {x y z : Carrier} → x ≤ hasSups.s (y ⇀ z) → y * x ≤ z
  adjunctionFrom {x} {y} {z} = λ x≤[y,z] → {!!}
