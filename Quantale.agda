{-# OPTIONS --without-K #-}

module Quantale where

open import Algebra.Lattice.Bundles

open import Algebra.Core
open import Algebra.Structures
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel; IsPartialOrder; IsEquivalence; Minimum)
open import Data.Product
open import Data.Sum
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
      -- actually it's an iff:
      isLUB' : ∀ t → s ≤ t → s isUpperBound

  open Sup public

record IsCompleteJSL {c ℓ e} {Carrier : Set c} (_≈_ : Rel Carrier e) (_≤_ : Rel Carrier ℓ) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Sup-Poset Carrier _≤_ public
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    sup            : ∀ Carrier → Sup {e = e} Carrier

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


record Quantale c ℓ e : Set (suc (c ⊔ ℓ ⊔ e)) where
  infix 4 _≈_ _≤_
  infix 5 _*_
  field
    -- order structure
    Carrier       : Set c
    _≈_           : Rel Carrier e
    _≤_           : Rel Carrier ℓ
    isCompleteJSL : IsCompleteJSL _≈_ _≤_
    -- semigroup structure
    _*_           : Op₂ Carrier
    isSemigroup   : IsSemigroup _≈_ _*_

  open IsCompleteJSL isCompleteJSL public renaming (refl to refl≤; trans to trans≤) hiding (reflexive; isEquivalence)
  open IsSemigroup isSemigroup     public renaming (refl to refl≈; trans to trans≈)

  -- generic action on the elements identified by a predicate
  P-op : (f : Carrier → Carrier) → (Carrier → Set (c ⊔ ℓ ⊔ e)) → (Carrier → Set (c ⊔ ℓ ⊔ e))
  P-op f P = (λ i → ∃[ p ] (P p × i ≈ f p))

  field
    distrˡ        : ∀ P x → x * (⋁ P) ≈ ⋁ (P-op (x *_) P)
    distrʳ        : ∀ P x → (⋁ P) * x ≈ ⋁ (P-op (_* x) P)

{-
module Minima {c a b} (Q : Quantale c a b) where

  open Quantale Q

  subst : ∀ {A : Set c} (_∼_ : Rel A a) {x y} → (eq : IsEquivalence _∼_) → x ≡ y → x ∼ y
  subst _∼_ record { refl = refl ; sym = _ ; trans = _ } p rewrite p = refl

  -- ^ is this really necessary? IsPartialOrder _≈_ _≤_ should provide something like this, and a ≈-≤-cong...

  open import Data.Empty.Polymorphic renaming (⊥ to ∅; ⊥-elim to ∅-elim)

  postulate
    ⊥-initial : {A : Set c} {f : (∅ {c ⊔ b}) → A} → f ≡ ∅-elim

  ⊥ : Carrier
  ⊥ = ⋁ ∅ ∅-elim

  ⊥-min : Minimum _≤_ ⊥
  ⊥-min = λ t → isLUB (sup ∅ ∅-elim) t ∅-elim

  ⊥-absorbsˡ : ∀ (x : Carrier) → x * ⊥ ≈ ⊥
  ⊥-absorbsˡ x =
    begin x * ⊥                 ≈⟨ distrˡ ∅ ∅-elim x ⟩
          {!   !}   ≈⟨ {!   !} ⟩
          {!   !}  ≈⟨ {!   !} ⟩
          ⊥           ∎
    where open import Relation.Binary.Reasoning.Setoid setoid


  record MinPoset : Set (suc (c ⊔ a ⊔ b)) where
    field
      ⊥     : Carrier
      isMin : ∀ {t : Carrier} → ⊥ ≤ t

    { bot = ⋁ ∅ ∅-elim
    ; isMin = λ {t} → isLUB (sup ∅ ∅-elim) t ∅-elim
    }

  module min = de min

  ⊥-absorbsˡ : ∀ (x : Carrier) → x * min.bot ≈ min.bot
  ⊥-absorbsˡ x =
    begin x * min.bot       ≈⟨ distrˡ ⊥ ⊥-elim x ⟩
          ⋁ ⊥ ((x *_) ∘ ⊥-elim) ≈⟨ {!   !} ⟩
          ⋁ ⊥ ⊥-elim            ≈⟨ {!   !} ⟩
          min.bot           ∎
    where pof = Eq.cong (λ t → (⋁ ⊥ t)) ⊥-initial
          open de min
          open import Relation.Binary.Reasoning.Setoid setoid

open Minima

module _ {c a b} (Q : Quantale c a b) where

  open Quantale Q

  open import Relation.Binary.Reasoning.PartialOrder (record { Carrier =  Carrier ; _≈_ = _≈_ ; _≤_ = _≤_ ; isPartialOrder = isPartialOrder })

  data ⊤ : Set (c ⊔ b) where
    ● : ⊤


  sup⊤ : ∀ {f : ⊤ → Carrier} → (⋁ ⊤ f) ≈ f ●
  sup⊤ {f} = antisym dis dat
    where dis : (⋁ _ _) ≤ f ●
          dis = isLUB ⋁ (f ●) (λ { ● → IsPartialOrder.refl isPartialOrder})
          dat : f ● ≤ s ⋁
          dat = isUB ⋁ ●
-}

module Exponentials {c ℓ e} (Q : Quantale c ℓ e) where

  open Quantale Q

  open import Agda.Builtin.Sigma
  -- TODO: import different reasonings locally to avoid clash
  -- TODO: that record is very verbose; is there a better way?


  yonedino′ : {x y z : Carrier}
         → (∀ z → ((y ≤ z) → (x ≤ z)))
         → x ≤ y
  yonedino′ {x} {y} {z} f = f y refl≤

  yonedino : {x y z : Carrier}
         → (∀ z → ((z ≤ x) → (z ≤ y)))
         → x ≤ y
  yonedino {x} {y} {z} f = f x refl≤

  yoneda : {x y : Carrier}
         → (∀ z → ((z ≤ x) → (z ≤ y)) × ((z ≤ y) → (z ≤ x)))
         → x ≈ y
  yoneda {x} {y} f = antisym (proj₁ (f x) refl≤) (proj₂ (f y) refl≤)

  ∨-predicate : Carrier → Carrier → Carrier → Set (c ⊔ ℓ ⊔ e)
  ∨-predicate a b = (λ p → Level.Lift (c ⊔ ℓ ⊔ e) ((a ≈ p) ⊎ (b ≈ p)))

  _∨_ : Carrier → Carrier → Carrier
  a ∨ b = ⋁ (∨-predicate a b)

  _∨ₛ_ : (a : Carrier) → (b : Carrier) → Sup (∨-predicate a b)
  a ∨ₛ b = sup (∨-predicate a b)

  ≤→a∨b≈b : ∀ {a} {b}
          → a ≤ b
          → a ∨ b ≈ b
  ≤→a∨b≈b {a} {b} a≤b =
    antisym (isLUB (a ∨ₛ b) b λ { x (lift (inj₁ a≈x)) → ≤-respˡ-≈ a≈x a≤b
                                ; x (lift (inj₂ b≈x)) → ≤-respˡ-≈ b≈x refl≤ })
            (isUB (a ∨ₛ b) b (lift (inj₂ refl≈)))

  a∨b≈b→≤ : ∀ {a} {b}
          → a ∨ b ≈ b
          → a ≤ b
  a∨b≈b→≤ {a} {b} a∨b≈b = ≤-respʳ-≈ a∨b≈b (isUB (a ∨ₛ b) a (lift (inj₁ refl≈)))

  sup-ext : ∀ {f} {g}
              → (∀ i → (f i → g i))
              → (⋁ f) ≤ (⋁ g)
  sup-ext {f} {g} fi→gi = isLUB (sup f) (⋁ g) λ x fx → isUB (sup g) x (fi→gi x fx)

  sup-extensionality : ∀ {f} {g}
              → (∀ i → (f i → g i) × (g i → f i))
              → (⋁ f) ≈ (⋁ g)
  sup-extensionality {f} {g} fi⇔gi = yoneda
    λ z → (λ z≤ → trans≤ z≤ (sup-ext (proj₁ ∘ fi⇔gi)))
        , (λ z≤ → trans≤ z≤ (sup-ext (proj₂ ∘ fi⇔gi)))

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
  counit-lemmaʳ {x} {y} = {!   !}
--    begin (x ↼ y) * x          ≈⟨ distrʳ _ y ⟩
--          ⋁ _          ≤⟨ ? ⟩
--          y ∎
--
  unit-lemmaˡ : ∀ {x y} → y ≤ (x ⇀ (x * y))
  unit-lemmaˡ {x} {y} =
    begin y             ≤⟨ isUB (x ⇀ₛ (x * y)) y (lift refl≤) ⟩
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
  adjunctionToˡ {x} {y} {z} y*x≤z = {!   !}

  int-adjunctionˡ : ∀ {x y z} → (y ⇀ (x ⇀ z)) ≈ ((x * y) ⇀ z)
  int-adjunctionˡ {x} {y} {z} = {!!}
  int-adjunctionˡ {x} {y} {z} = sup-extensionality λ i →
      (λ { (lift p) → lift (≤-respˡ-≈ (Eq.sym (assoc _ _ _)) (adjunctionFromˡ p)) })
    , (λ { (lift p) → lift (adjunctionToˡ (≤-respˡ-≈ (assoc _ _ _) p)) })

  int-adjunctionʳ : ∀ {x y z} → (y ↼ (x ↼ z)) ≈ ((y * x) ⇀ z)
  int-adjunctionʳ {x} {y} {z} = {!!}

{-
  adjunctionToˡ : {x y z : Carrier} → y * x ≤ z → x ≤ y ⇀ z
  adjunctionToˡ {x} {y} {z} y*x≤z = isUB (y ⇀ₛ z) (x , y*x≤z)

  adjunctionFromˡ : {x y z : Carrier} → x ≤ (y ⇀ z) → y * x ≤ z
  adjunctionFromˡ {x} {y} {z} x≤[y,z] =
    begin y * x       ≤⟨ {!   !} ⟩
          {!   !}           ≤⟨ {!   !} ⟩
          z           ∎

  -- adjunction properties, left hom
  counit-lemmaʳ : {x y : Carrier} → (x ↼ y) * x ≤ y
  counit-lemmaʳ {x} {y} =
    begin (x ↼ y) * x          ≈⟨ distrʳ _ proj₁ x ⟩
          ⋁ _ ((_* x) ∘ proj₁) ≤⟨ isLUB (sup _ _) y proj₂ ⟩
          y                    ∎

  unit-lemmaʳ : {x y : Carrier} → y ≤ (x ⇀ (x * y))
  unit-lemmaʳ {x} {y} =
    begin y             ≤⟨ isUB (_ ⇀ₛ _) (y , refl≤) ⟩
          (x ⇀ (x * y)) ∎

  adjunctionToʳ : {x y z : Carrier} → x * y ≤ z → x ≤ (y ↼ z)
  adjunctionToʳ {x} {y} {z} x*y≤z = isUB (y ↼ₛ z) (x , x*y≤z)

  adjunctionFromʳ : {x y z : Carrier} → x ≤ (y ↼ z) → x * y ≤ z
  adjunctionFromʳ {x} {y} {z} x≤[y,z] =
    begin x * y       ≤⟨ *-congʳ x≤[y,z] ⟩
          (y ↼ z) * y ≤⟨ counit-lemmaʳ ⟩
          z           ∎

  sup-functor : {I : Set (c ⊔ b)} {f g : I → Carrier}
              → (∀ {i : I} → f i ≤ g i)
              → ((⋁ I f))
              ≤ ((⋁ I g))
  sup-functor {I} {f} {g} fi≤gi = begin (⋁ I f) ≤⟨ {!  !} ⟩ --isLUB (⋁ _ _) ((⋁ I g)) (λ t → clop) ⟩
                                      (⋁ I g) ∎
                                      where clop : {t : I} → f t ≤ (⋁ I g)
                                            clop {t} = begin f t ≤⟨ fi≤gi ⟩ g t ≤⟨ {!   !} ⟩ {!   !} ∎ --isUB (⋁ _ _) t ⟩ (⋁ _ _) ∎

  lemma-cong : ∀ {A : Set (c ⊔ b)} {P Q : A → Carrier}
             → (∀ x → P x ≈ Q x)
             → (⋁ A P)
             ≈ (⋁ A Q)
  lemma-cong {A} {P} {Q} e = antisym l r
    where
      open import Relation.Binary.Reasoning.Setoid setoid
      l : (⋁ A P) ≤ (⋁ A Q)
      l = {!   !} --isLUB (⋁ A P) ((⋁ A Q)) λ i → trans< (≤-respˡ-≈ (sym (e i)) refl≤) (isUB (⋁ A Q) i)
      r : (⋁ A Q) ≤ (⋁ A P)
      r = {!   !} --isLUB (⋁ A Q) ((⋁ A P)) λ i → trans< (≤-respˡ-≈ ((e i)) refl≤) (isUB (⋁ A P) i)

  lemma-cong-sigma1 : ∀ {A} {B} {i} {j}
             → ((A → B))
             → (⋁ A i)
             ≤ (⋁ B j)
  lemma-cong-sigma1 {A} {B} e = yonedino λ z x → {!   !}


  lemma-impl : ∀ {A} {B}
             → (∀ x → (A x → B x) × (B x → A x))
             → Sup c b A
             → ⋁ (Σ Carrier B) proj₁
  lemma-impl {A} {B} e = ?

  lemma-cong-sigma : ∀ {A} {B}
             → (∀ x → (A x → B x) × (B x → A x))
             → (⋁ (Σ Carrier A) proj₁)
             ≈ (⋁ (Σ Carrier B) proj₁)
  lemma-cong-sigma {A} {B} e =
    yoneda λ w → (λ w≤ → isUB (⋁ {!   !} proj₁) (w , {!   !})) , {!   !}


-}



--    yoneda λ w →
--      (λ w≤ → isUB (⋁ (supfun (x * y) z) proj₁)
--                   (w , adjunctionFromˡ (trans< w≤ (trans< {!   !} {!   !})))) ,
--      {!   !}
--
--     w ≤ (⋁ (Σ Carrier (λ t → (x * y) * t ≤ z)) fst)
--w≤ : w ≤ (⋁ (Σ Carrier (λ t →       y * t  ≤ s (x ⇀ z)))  fst)


{-



  -- IsPartialOrder.antisym isPartialOrder dis dat
   where
    supfun = λ p q → Σ Carrier (λ t → p * t ≤ q)


    seppia : (i : supfun y (s (x ⇀ z))) → fst i ≤ s ((x * y) ⇀ z)
    seppia (t , y*t≤[x,z]) = let r = adjunctionFromˡ (isUB (⋁ _ _) ({!   !} , {!   !})) in {!   !}


    --adjunctionToˡ (isUB (⋁ {supfun (x * y) z} {λ { (c , p) → {!   !} }}) {!   !})
    -- isUB (⋁ {supfun {!   !} z} {proj₁}) (t , (adjunctionFromˡ (isUB ⋁ {!   !})))

    dis : s (y ⇀ s (x ⇀ z)) ≤ s ((x * y) ⇀ z)
    dis = {!   !}
    --isLUB (⋁ (supfun y (s (x ⇀ z))) proj₁) (s ((x * y) ⇀ z)) seppia

    dat : s ((x * y) ⇀ z) ≤ s (y ⇀ s (x ⇀ z))
    dat = {!  !}


    y → (x → z) ≤ (x * y) → z

    LHS = sup {t : y * t ≤ x → z} < isUB >
          ∀ t → y * t ≤ x → z     < adjunctionFromˡ >
           x * (y * t) ≤ z =< assoc >
           (x * y) * t ≤ z ≤< isUB >
           sup {t : (x * y) * t ≤ z}

    y ⇀ s (x ⇀ z)
-}
