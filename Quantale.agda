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
    s     : P
    isUB  : ∀ (i : I) → (f i) ≤ s
    isLUB : (t : P) → (∀ (i : I) → f i ≤ t) → s ≤ t

open module S = hasSups

record IsCompleteJSL {c ℓ ℓ'} {A : Set c} (_≈_ : Rel A ℓ) (_≤_ : Rel A ℓ') : Set (suc (c ⊔ ℓ ⊔ ℓ')) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    sups           : ∀ {I : Set (c ⊔ ℓ')} {f : I → A} → hasSups c ℓ' I A (_≤_) f
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
    distrˡ        : (I : Set (c ⊔ ℓ')) (y : I → Carrier) (x : Carrier) → (x * s (sups {I} {y})) ≈ s (sups {I} {λ i → x * (y i)})
    distrʳ        : (I : Set (c ⊔ ℓ')) (y : I → Carrier) (x : Carrier) → (s (sups {I} {y})) * x ≈ s (sups {I} {λ i → (y i) * x})
  open IsSemigroup isSemigroup public


module Minima {c a b} (Q : Quantale c a b) where

  open module zap = Quantale Q
  open import Relation.Binary.Reasoning.Setoid setoid
  open import Agda.Builtin.Sigma

  postulate
    ⊥-initial : {A : Set c} {f : (⊥ {c ⊔ b}) → A} → f ≡ ⊥-elim

  subst : ∀ {A : Set c} (_∼_ : Rel A a) {x y} → (eq : IsEquivalence _∼_) → x ≡ y → x ∼ y
  subst _∼_ record { refl = refl ; sym = _ ; trans = _ } p rewrite p = refl

  -- ^ is this really necessary? IsPartialOrder _≈_ _≤_ should provide something like this, and a ≈-≤-cong...

  record min : Set (suc (c ⊔ a ⊔ b)) where
    field
      bot   : Carrier
      isMin : ∀ {t : Carrier} → bot ≤ t

  has⊥ : min
  has⊥ = record
    { bot = s emptyFamily
    ; isMin = λ {t} → isLUB emptyFamily t ⊥-elim
    }
    where
      emptyFamily : _
      emptyFamily = (IsCompleteJSL.sups isCompleteJSL) {⊥} {⊥-elim}

  ⊥-absorbsˡ : ∀ (x : Carrier) → x * (min.bot has⊥) ≈ (min.bot has⊥)
  ⊥-absorbsˡ x =
    begin x * min.bot has⊥                            ≈⟨ distrˡ ⊥ ⊥-elim x ⟩
          s (sups {⊥} {λ i → x * (⊥-elim i)}) ≈⟨ subst _≈_ isEquivalence pof ⟩
          s (sups {⊥} {⊥-elim})               ≈⟨ subst _≈_ isEquivalence _≡_.refl ⟩
          min.bot has⊥                                ∎
    where pof = Eq.cong (λ t → s (sups {⊥} {t})) ⊥-initial

open Minima

{-
module _ {c a b} (Q : Quantale c a b) where

  open module zup = Quantale Q

  open import Agda.Builtin.Sigma
  open import Relation.Binary.Reasoning.PartialOrder (record { Carrier =  Carrier ; _≈_ = _≈_ ; _≤_ = _≤_ ; isPartialOrder = isPartialOrder })

  sup-functor : {I : Set (c ⊔ b)} {f g : I → Carrier} → (∀ {i : I} → f i ≤ g i) → (s (sups {I} {f})) ≤ (s (sups {I} {g}))
  sup-functor {I} {f} {g} fi≤gi = begin s (sups {I} {f}) ≤⟨ isLUB sups (s (sups {I} {g})) (λ t → clop) ⟩
                                      s (sups {I} {g}) ∎
                                      where clop : {t : I} → f t ≤ s (sups {I} {g})
                                            clop {t} = begin f t ≤⟨ fi≤gi ⟩ g t ≤⟨ isUB sups t ⟩ s (sups) ∎

  data ⊤ : Set (c ⊔ b) where
    ● : ⊤

  sup⊤ : ∀ {f : ⊤ → Carrier} → s (sups {⊤} {f}) ≈ f ●
  sup⊤ {f} = antisym dis dat
    where dis : s sups ≤ f ●
          dis = isLUB sups (f ●) (λ { ● → IsPartialOrder.refl isPartialOrder})
          dat : f ● ≤ s sups
          dat = isUB sups ●
-}

module Exponentials {c a b} (Q : Quantale c a b) where

  open module zop = Quantale Q

  open import Agda.Builtin.Sigma
  open import Relation.Binary.Reasoning.PartialOrder
    (record { Carrier =  Carrier
            ; _≈_ = _≈_
            ; _≤_ = _≤_
            ; isPartialOrder = isPartialOrder
            })
  -- TODO: import different reasonings locally to avoid clash
  -- TODO: that record is very verbose; is there a better way?
  postulate
    *-congˡ : (x y z : Carrier) → y ≤ z → x * y ≤ x * z
  -- TODO: probably provable?

  -- left internal hom
  _⇀_ : (p : Carrier) → (q : Carrier) →
    hasSups c b (Σ Carrier (λ x → p * x ≤ q)) Carrier _≤_ (λ ( x , _ ) → x)
  p ⇀ q = sups {supfun p q} {λ {(x , _ ) → x}}
    where supfun = λ p q → Σ Carrier (λ t → p * t ≤ q)

  -- right internal hom
  _↼_ : (p : Carrier) → (q : Carrier) →
    hasSups c b (Σ Carrier (λ x → x * p ≤ q)) Carrier _≤_ (λ ( x , _ ) → x)
  p ↼ q = sups {supfun p q} {λ {(x , _ ) → x}}
    where supfun = λ p q → Σ Carrier (λ t → t * p ≤ q)

  -- adjunction properties
  adjunctionToˡ : {x y z : Carrier} → y * x ≤ z → x ≤ s (y ⇀ z)
  adjunctionToˡ {x} {y} {z} y*x≤z = isUB adjsup ( x , y*x≤z )
    where adjsup = sups {Σ Carrier (λ x → y * x ≤ z)} {λ {(x , _ ) → x}}

  counit-lemma : {x y : Carrier} → x * s (x ⇀ y) ≤ y
  counit-lemma {x} {y} =
    begin (x * s (x ⇀ y))                          ≈⟨ distrˡ supfun ( λ {( x , _ ) → x}) x ⟩
          s (sups {supfun} {λ {(t , _ ) → x * t}}) ≤⟨ isLUB sups y (λ { ( _ , proof) → proof}) ⟩
          y                                                ∎
    where supfun = Σ Carrier (λ t → x * t ≤ y)
  adjunctionFromˡ : {x y z : Carrier} → x ≤ s (y ⇀ z) → y * x ≤ z
  adjunctionFromˡ {x} {y} {z} x≤[y,z] =
    begin y * x         ≤⟨ *-congˡ y x (s (y ⇀ z)) x≤[y,z] ⟩
          y * s (y ⇀ z) ≤⟨ counit-lemma ⟩
          z                     ∎

  -- TODO: add adjunctionToʳ and adjunctionFromʳ