{-# OPTIONS --without-K #-}

module Quantale where

open import Algebra.Lattice.Bundles

open import Algebra.Core
open import Algebra.Structures
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel; IsPartialOrder; IsEquivalence; Minimum; Maximum)
open import Data.Product
open import Data.Sum
open import Algebra.Definitions
open import Level using (Lift; lift)
open import Function using (_∘_)
open import Data.Empty.Polymorphic using ()
open import Relation.Binary.Reasoning.Setoid using ()
open import Relation.Binary.PropositionalEquality using (_≡_; subst₂)

module Sup-Poset {c ℓ} (Carrier : Set c) (_≤_ : Rel Carrier ℓ) where

  record Sup {e} (P : Carrier → Set (c ⊔ ℓ ⊔ e)) : (Set (suc (c ⊔ ℓ ⊔ e))) where

    _isUpperBound : Carrier → Set (c ⊔ ℓ ⊔ e)
    s isUpperBound = ∀ x → P x → x ≤ s

    field
      s      : Carrier
      isUB   : s isUpperBound
      isLUB  : ∀ t → t isUpperBound → s ≤ t

  open Sup public

module Inf-Poset {c ℓ} (Carrier : Set c) (_≤_ : Rel Carrier ℓ) where

  record Inf {e} (P : Carrier → Set (c ⊔ ℓ ⊔ e)) : (Set (suc (c ⊔ ℓ ⊔ e))) where

    _isLowerBound : Carrier → Set (c ⊔ ℓ ⊔ e)
    s isLowerBound = ∀ x → P x → s ≤ x

    field
      s      : Carrier
      isLB   : s isLowerBound
      isGLB  : ∀ t → t isLowerBound → t ≤ s

  open Inf public

record IsCompleteJSL {c ℓ e} {Carrier : Set c} (_≈_ : Rel Carrier e) (_≤_ : Rel Carrier ℓ) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Sup-Poset Carrier _≤_ public
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    sup            : ∀ P → Sup {e = e} P

  ⋁ : ∀ P → Carrier
  ⋁ P = s (sup P)

  open IsPartialOrder isPartialOrder public

record CompleteJSL c ℓ e : Set (suc (c ⊔ ℓ ⊔ e)) where
  infix  4 _≈_ _≤_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier e
    _≤_           : Rel Carrier ℓ
    isCompleteJSL : IsCompleteJSL _≈_ _≤_
  open IsCompleteJSL isCompleteJSL public

record IsQuantale {c ℓ e} {Carrier : Set c} (_≈_ : Rel Carrier e) (_≤_ : Rel Carrier ℓ) (_*_ : Op₂ Carrier) : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    -- order structure
    isCompleteJSL : IsCompleteJSL _≈_ _≤_
    -- semigroup structures
    isSemigroup   : IsSemigroup _≈_ _*_

  open IsCompleteJSL isCompleteJSL public renaming (refl to refl≤; trans to trans≤) hiding (reflexive; isEquivalence)
  open IsSemigroup isSemigroup     public renaming (refl to refl≈; trans to trans≈)

  -- generic action on the elements of a predicate
  P-op : (f : Carrier → Carrier) → (Carrier → Set (c ⊔ ℓ ⊔ e)) → (Carrier → Set (c ⊔ ℓ ⊔ e))
  P-op f P = (λ i → ∃[ p ] (P p × i ≈ f p))

  field
    distrˡ        : ∀ P x → (x * (⋁ P)) ≈ (⋁ (P-op (x *_) P))
    distrʳ        : ∀ P x → ((⋁ P) * x) ≈ (⋁ (P-op (_* x) P))

record Quantale c ℓ e : Set (suc (c ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ _≤_
  infix 5 _*_
  field
    -- order structure
    Carrier       : Set c
    _≈_           : Rel Carrier e
    _≤_           : Rel Carrier ℓ
    _*_           : Op₂ Carrier
    isQuantale    : IsQuantale _≈_ _≤_ _*_

  open IsQuantale isQuantale public


module Properties {c ℓ e} (Q : Quantale c ℓ e) where

  open Quantale Q

  ∨-predicate : Carrier → Carrier → Carrier → Set (c ⊔ ℓ ⊔ e)
  ∨-predicate a b = (λ p → Level.Lift (c ⊔ ℓ ⊔ e) ((a ≈ p) ⊎ (b ≈ p)))

  _∨_ : Carrier → Carrier → Carrier
  a ∨ b = ⋁ (∨-predicate a b)

  ≤→a∨b≈b : ∀ {a} {b}
          → a ≤ b
          → a ∨ b ≈ b
  ≤→a∨b≈b {a} {b} a≤b =
    antisym (isLUB (sup _) b λ { x (lift (inj₁ a≈x)) → ≤-respˡ-≈ a≈x a≤b
                                ; x (lift (inj₂ b≈x)) → ≤-respˡ-≈ b≈x refl≤ })
            (isUB (sup _) b (lift (inj₂ refl≈)))

  a∨b≈b→≤ : ∀ {a} {b}
          → a ∨ b ≈ b
          → a ≤ b
  a∨b≈b→≤ {a} {b} a∨b≈b = ≤-respʳ-≈ a∨b≈b (isUB (sup _) a (lift (inj₁ refl≈)))

  sup-ext : ∀ {f} {g}
              → (∀ i → (f i → g i))
              → (⋁ f) ≤ (⋁ g)
  sup-ext {f} {g} fi→gi = isLUB (sup f) (⋁ g) λ x fx → isUB (sup g) x (fi→gi x fx)

  sup-extensionality : ∀ {f} {g}
              → (∀ i → (f i → g i) × (g i → f i))
              → (⋁ f) ≈ (⋁ g)
  sup-extensionality {f} {g} fi⇔gi =
    antisym
      (sup-ext (proj₁ ∘ fi⇔gi))
      (sup-ext (proj₂ ∘ fi⇔gi))

  *-congˡ : ∀ {a x y}
          → x ≤ y
          → a * x ≤ a * y
  *-congˡ {a} {x} {y} x≤y =
    let
        convert-P-op : ((a * x) ∨ (a * y)) ≈ ⋁ (P-op (a *_) (∨-predicate x y))
        convert-P-op = Eq.sym (sup-extensionality
               (λ i → (λ { (t , lift (inj₁ r) , k) → lift (inj₁ (trans≈ (∙-congˡ r) (Eq.sym k)))
                         ; (t , lift (inj₂ r) , k) → lift (inj₂ (trans≈ (∙-congˡ r) (Eq.sym k))) })
                    , (λ { (lift (inj₁ a*x≈i)) → x , lift (inj₁ refl≈) , Eq.sym a*x≈i
                         ; (lift (inj₂ a*y≈i)) → y , lift (inj₂ refl≈) , Eq.sym a*y≈i })))

        t : (a * x) ∨ (a * y) ≈ a * y
        t =
          let open Relation.Binary.Reasoning.Setoid setoid in
          begin (a * x) ∨ (a * y)                 ≈⟨ convert-P-op ⟩
                ⋁ (P-op (a *_) (∨-predicate x y)) ≈⟨ Eq.sym (distrˡ ((∨-predicate x y)) a)  ⟩
                a * (x ∨ y)                       ≈⟨ ∙-congˡ (≤→a∨b≈b x≤y) ⟩
                a * y                             ∎
        in a∨b≈b→≤ t

  *-congʳ : ∀ {a x y}
          → x ≤ y
          → x * a ≤ y * a
  *-congʳ {a} {x} {y} x≤y =
    let
        convert-P-op : ((x * a) ∨ (y * a)) ≈ ⋁ (P-op (_* a) (∨-predicate x y))
        convert-P-op = Eq.sym (sup-extensionality
               (λ i → (λ { (t , lift (inj₁ r) , k) → lift (inj₁ (trans≈ (∙-congʳ r) (Eq.sym k)))
                         ; (t , lift (inj₂ r) , k) → lift (inj₂ (trans≈ (∙-congʳ r) (Eq.sym k))) })
                    , (λ { (lift (inj₁ a*x≈i)) → x , lift (inj₁ refl≈) , Eq.sym a*x≈i
                         ; (lift (inj₂ a*y≈i)) → y , lift (inj₂ refl≈) , Eq.sym a*y≈i })))

        t : (x * a) ∨ (y * a) ≈ y * a
        t =
          let open Relation.Binary.Reasoning.Setoid setoid in
          begin (x * a) ∨ (y * a)                 ≈⟨ convert-P-op ⟩
                ⋁ (P-op (_* a) (∨-predicate x y)) ≈⟨ Eq.sym (distrʳ ((∨-predicate x y)) a)  ⟩
                (x ∨ y) * a                       ≈⟨ ∙-congʳ (≤→a∨b≈b x≤y) ⟩
                y * a                             ∎
        in a∨b≈b→≤ t

module Exponentials {c ℓ e} (Q : Quantale c ℓ e) where

  open Quantale Q
  open Properties Q

  -- left internal hom
  _⇀_ : Carrier → Carrier → Carrier
  p ⇀ q = ⋁ (λ t → Level.Lift (c ⊔ ℓ ⊔ e) (p * t ≤ q))

  -- right internal hom
  _↼_ : Carrier → Carrier → Carrier
  p ↼ q = ⋁ (λ t → Level.Lift (c ⊔ ℓ ⊔ e) (t * p ≤ q))

  -- left internal hom, whole record
  _⇀ₛ_ : (p : Carrier) → (q : Carrier) → Sup (λ t → Level.Lift (c ⊔ ℓ ⊔ e) (p * t ≤ q))
  p ⇀ₛ q = sup (λ t → Level.Lift (c ⊔ ℓ ⊔ e) (p * t ≤ q))

  -- right internal hom, whole record
  _↼ₛ_ : (p : Carrier) → (q : Carrier) → Sup (λ t → Level.Lift (c ⊔ ℓ ⊔ e) (t * p ≤ q))
  p ↼ₛ q = sup (λ t → Level.Lift (c ⊔ ℓ ⊔ e) (t * p ≤ q))

  ⇀-congˡ  : ∀ {a x y}
          → x ≤ y
          → a ⇀ x ≤ a ⇀ y
  ⇀-congˡ {a} {x} {y} x≤y = sup-ext λ { i (lift a*i≤x) → lift (trans≤ a*i≤x x≤y) }

  ↼-congˡ  : ∀ {a x y}
          → x ≤ y
          → a ↼ x ≤ a ↼ y
  ↼-congˡ {a} {x} {y} x≤y = sup-ext λ { i (lift a*i≤x) → lift (trans≤ a*i≤x x≤y) }

  ⇀-congʳ : ∀ {a x y}
          → y ≤ x
          → x ⇀ a ≤ y ⇀ a
  ⇀-congʳ {a} {x} {y} x≤y = sup-ext λ { i (lift x*i≤a) → lift (trans≤ (*-congʳ x≤y) x*i≤a) }

  ↼-congʳ : ∀ {a x y}
          → y ≤ x
          → x ↼ a ≤ y ↼ a
  ↼-congʳ {a} {x} {y} x≤y = sup-ext λ { i (lift x*i≤a) → lift (trans≤ (*-congˡ x≤y) x*i≤a) }

  open import Relation.Binary.Reasoning.PartialOrder
    (record { Carrier =  Carrier
            ; _≈_ = _≈_
            ; _≤_ = _≤_
            ; isPartialOrder = isPartialOrder
            })

  -- adjunction properties, left hom
  counit-lemmaˡ : ∀ {x y} → x * (x ⇀ y) ≤ y
  counit-lemmaˡ {x} {y} =
    begin x * (x ⇀ y) ≈⟨ distrˡ _ x ⟩
          ⋁ _         ≤⟨ isLUB (sup _) y (λ { t (o , lift k , e) → ≤-respˡ-≈ (sym e) k }) ⟩
          y           ∎

  -- adjunction properties, left hom
  counit-lemmaʳ : {x y : Carrier} → (x ↼ y) * x ≤ y
  counit-lemmaʳ {x} {y} =
    begin (x ↼ y) * x ≈⟨ distrʳ _ x ⟩
          ⋁ _         ≤⟨ isLUB (sup _) y (λ { t (o , lift k , e) → ≤-respˡ-≈ (sym e) k }) ⟩
          y           ∎

  unit-lemmaˡ : ∀ {x y} → y ≤ (x ⇀ (x * y))
  unit-lemmaˡ {x} {y} =
    begin y             ≤⟨ isUB (sup _) y (lift refl≤) ⟩
          (x ⇀ (x * y)) ∎

  adjunctionFromˡ : ∀ {x y z} → x ≤ (y ⇀ z) → y * x ≤ z
  adjunctionFromˡ {x} {y} {z} x≤[y,z] =
    begin y * x       ≤⟨ *-congˡ x≤[y,z] ⟩
          y * (y ⇀ z) ≤⟨ counit-lemmaˡ ⟩
          z           ∎

  adjunctionFromʳ : {x y z : Carrier} → x ≤ (y ↼ z) → x * y ≤ z
  adjunctionFromʳ {x} {y} {z} x≤[y,z] =
    begin x * y       ≤⟨ *-congʳ x≤[y,z] ⟩
          (y ↼ z) * y ≤⟨ counit-lemmaʳ ⟩
          z           ∎

  adjunctionToˡ : {x y z : Carrier} → y * x ≤ z → x ≤ y ⇀ z
  adjunctionToˡ {x} {y} {z} y*x≤z = isUB (sup _) x (lift y*x≤z)

  adjunctionToʳ : {x y z : Carrier} → x * y ≤ z → x ≤ (y ↼ z)
  adjunctionToʳ {x} {y} {z} x*y≤z = isUB (sup _) x (lift x*y≤z)

  -- the adjunction (x * _ ⊣ x ⇀ _) in a quantale internalizes
  int-adjunctionˡ : ∀ {x y z} → (y ⇀ (x ⇀ z)) ≈ ((x * y) ⇀ z)
  int-adjunctionˡ {x} {y} {z} = sup-extensionality λ i →
      (λ { (lift p) → lift (≤-respˡ-≈ (Eq.sym (assoc _ _ _)) (adjunctionFromˡ p)) })
    , (λ { (lift p) → lift (adjunctionToˡ (≤-respˡ-≈ (assoc _ _ _) p)) })

  int-adjunctionʳ : ∀ {x y z} → (y ↼ (x ↼ z)) ≈ ((y * x) ↼ z)
  int-adjunctionʳ {x} {y} {z} = sup-extensionality λ i →
      (λ { (lift p) → lift (≤-respˡ-≈ (assoc _ _ _) (adjunctionFromʳ p)) })
    , (λ { (lift p) → lift (adjunctionToʳ (≤-respˡ-≈ (Eq.sym (assoc _ _ _)) p)) })

  -- the way left and right hom interact
  LR-hom : ∀ {x y z} → x ⇀ (y ↼ z) ≈ y ↼ (x ⇀ z)
  LR-hom {x} {y} {z} = sup-extensionality λ i →
      (λ {(lift x*i≤y↼z) → lift (adjunctionToˡ (≤-respˡ-≈ (assoc x i y) (adjunctionFromʳ x*i≤y↼z)))})
    , λ {(lift i*y≤x⇀z) → lift (adjunctionToʳ (≤-respˡ-≈ (Eq.sym (assoc _ _ _)) (adjunctionFromˡ i*y≤x⇀z)))}

  thm6 : ∀ {a b} → a * (a ⇀ b) ≈ b → ∃[ c ] a * c ≈ b
  thm6 {a} {b} *a⇀b≈b = (a ⇀ b) , *a⇀b≈b

  thm6′ : ∀ {a b} → ∃[ c ] a * c ≈ b → a * (a ⇀ b) ≈ b
  thm6′ {a} {b} (c , a*c≈b) = antisym counit-lemmaˡ (trans≤ (≤-respˡ-≈ a*c≈b refl≤) (*-congˡ (isUB (sup _) c (lift (≤-respʳ-≈ a*c≈b refl≤)))))

  thm7 : ∀ {a b} → (a ↼ b) * a ≈ b → ∃[ c ] c * a ≈ b
  thm7 {a} {b} *a↼b≈b = (a ↼ b) , *a↼b≈b

  thm7′ : ∀ {a b} → ∃[ c ] c * a ≈ b → (a ↼ b) * a ≈ b
  thm7′ {a} {b} (c , a*c≈b) = antisym counit-lemmaʳ (trans≤ (≤-respˡ-≈ a*c≈b refl≤) (*-congʳ (isUB (sup _) c (lift (≤-respʳ-≈ a*c≈b refl≤)))))

  thm8 : ∀ {a b} → a ⇀ (a * b) ≈ b → ∃[ c ] a ⇀ c ≈ b
  thm8 {a} {b} a⇀a*b≈b = (a * b) , a⇀a*b≈b

  thm8′ : ∀ {a b} → ∃[ c ] a ⇀ c ≈ b → a ⇀ (a * b) ≈ b
  thm8′ {a} {b} (c , a⇀c≈b) = antisym (≤-respʳ-≈ a⇀c≈b (⇀-congˡ (≤-respˡ-≈ (∙-congˡ a⇀c≈b) counit-lemmaˡ))) (adjunctionToˡ refl≤)

  thm9 : ∀ {a b} → a ↼ (b * a) ≈ b → ∃[ c ] a ↼ c ≈ b
  thm9 {a} {b} a↼a*b≈b = (b * a) , a↼a*b≈b

  thm9′ : ∀ {a b} → ∃[ c ] a ↼ c ≈ b → a ↼ (b * a) ≈ b
  thm9′ {a} {b} (c , a↼c≈b) = antisym (≤-respʳ-≈ a↼c≈b (↼-congˡ (≤-respˡ-≈ (∙-congʳ a↼c≈b) counit-lemmaʳ))) (adjunctionToʳ refl≤)

  lemmaʳ : ∀ {a b c} → c ⇀ a ≈ b → c ≤ b ↼ a
  lemmaʳ {a} {b} {c} c⇀a≈b = isUB (sup _) c (lift (≤-respˡ-≈ (∙-congˡ c⇀a≈b) (counit-lemmaˡ {c} {a})))

  lemmaˡ : ∀ {a b c} → c ↼ a ≈ b → c ≤ b ⇀ a
  lemmaˡ {a} {b} {c} c↼a≈b = isUB (sup _) c (lift (≤-respˡ-≈ (∙-congʳ c↼a≈b) (counit-lemmaʳ {c} {a})))

  thm10 : ∀ {a b} → (b ↼ a) ⇀ a ≈ b → ∃[ c ] c ⇀ a ≈ b
  thm10 {a} {b} b↼a⇀a≈b = (b ↼ a) , b↼a⇀a≈b

  thm10′ : ∀ {a b} → ∃[ c ] c ⇀ a ≈ b → (b ↼ a) ⇀ a ≈ b
  thm10′ {a} {b} (c , c⇀a≈b) = antisym (≤-respʳ-≈ c⇀a≈b (⇀-congʳ (lemmaʳ c⇀a≈b))) (isUB (sup _) b (lift counit-lemmaʳ))

  thm11 : ∀ {a b} → (b ⇀ a) ↼ a ≈ b → ∃[ c ] c ↼ a ≈ b
  thm11 {a} {b} b⇀a↼a≈b = (b ⇀ a) , b⇀a↼a≈b

  thm11′ : ∀ {a b} → ∃[ c ] c ↼ a ≈ b → (b ⇀ a) ↼ a ≈ b
  thm11′ {a} {b} (c , c⇀a≈b) = antisym (≤-respʳ-≈ c⇀a≈b (↼-congʳ (lemmaˡ c⇀a≈b))) (isUB (sup _) b (lift counit-lemmaˡ))


module Homomorphisms {c ℓ e} (P Q : Quantale c ℓ e) where
  open import Algebra.Morphism.Definitions
  open module P = Quantale P
  open module pP = Properties P

  open module Q = Quantale Q
  open module pQ = Properties Q

  record Supmap (f : P.Carrier → Q.Carrier) : Set (suc (c ⊔ ℓ ⊔ e)) where
    field
      isMagmaHomomorphism : Homomorphic₂ P.Carrier Q.Carrier Q._≈_ f P._*_ Q._*_
      _preserves-⋁ : ∀ {T : P.Carrier → Set (c ⊔ ℓ ⊔ e)} → f (P.⋁ T) Q.≈ Q.⋁ (λ x → Σ[ p ∈ P.Carrier ] (T p × (f p Q.≈ x)))

module BotTop {c a b} (Q : Quantale c a b) where

  open Quantale Q
  open Properties Q
  open import Data.Empty.Polymorphic renaming (⊥ to False)
  open import Data.Unit.Polymorphic renaming (⊤ to True)

  ⊥ : Carrier
  ⊥ = ⋁ (λ _ → False)

  ⊤ : Carrier
  ⊤ = ⋁ (λ _ → True)

  ⊥-min : Minimum _≤_ ⊥
  ⊥-min = λ x → isLUB (sup _) x λ t ()

  ⊤-max : Maximum _≤_ ⊤
  ⊤-max = λ x → isUB (sup _) x tt

  ⊥-absorbsˡ : ∀ (x : Carrier) → x * ⊥ ≈ ⊥
  ⊥-absorbsˡ x =
    begin x * ⊥                         ≈⟨ distrˡ (λ _ → False) x ⟩
          ⋁ (P-op (x *_) (λ _ → False)) ≈⟨ sup-extensionality (λ i → (λ ()) , λ ()) ⟩
          ⊥                             ∎
    where open import Relation.Binary.Reasoning.Setoid setoid
