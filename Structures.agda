{-# OPTIONS --without-K #-}

module Structures where

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
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; subst₂)

open import Quantale

record IsCommutativeQuantale {c} {ℓ} {e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q

  field
    isCommutative : Commutative _≈_ _*_

record CommutativeQuantale {c} {ℓ} {e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isCommutativeQuantale : IsCommutativeQuantale Q

  open IsCommutativeQuantale isCommutativeQuantale public

record IsUnitalQuantale {c} {ℓ} {e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q

  field
    i        : Carrier
    isUnital : Identity _≈_ i _*_

record UnitalQuantale {c} {ℓ} {e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isUnitalQuantale : IsUnitalQuantale Q

  open IsUnitalQuantale isUnitalQuantale public

record IsIdempotentQuantale {c} {ℓ} {e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q

  field
    isIdempotent : Idempotent _≈_ _*_

record IdempotentQuantale {c} {ℓ} {e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isIdempotentQuantale : IsIdempotentQuantale Q

  open IsIdempotentQuantale isIdempotentQuantale public

record IsRightSidedQuantale {c ℓ e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q public
  open BotTop Q
  field
    sidedʳ : ∀ {a : Carrier} → a * ⊤ ≤ a

record RightSidedQuantale {c ℓ e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isRightSidedQuantale : IsRightSidedQuantale Q

  open IsRightSidedQuantale isRightSidedQuantale public

record IsLeftSidedQuantale {c ℓ e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q public
  open BotTop Q
  field
    sidedˡ : ∀ {a : Carrier} → ⊤ * a ≤ a

record LeftSidedQuantale {c ℓ e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isLeftSidedQuantale : IsLeftSidedQuantale Q

  open IsLeftSidedQuantale isLeftSidedQuantale public

record IsStrictlyRightSidedQuantale {c ℓ e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q public
  open BotTop Q

  field
    strictSidedʳ : ∀ {a : Carrier} → a * ⊤ ≈ a

record StrictlyRightSidedQuantale {c ℓ e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isStrictlyRightSidedQuantale : IsStrictlyRightSidedQuantale Q

  open IsStrictlyRightSidedQuantale isStrictlyRightSidedQuantale public

record IsStrictlyLeftSidedQuantale {c ℓ e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q public
  open BotTop Q

  field
    strictSidedˡ : ∀ {a : Carrier} → ⊤ * a ≈ a

record StrictlyLeftSidedQuantale {c ℓ e} : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isStrictlyLeftSidedQuantale : IsStrictlyLeftSidedQuantale Q

  open IsStrictlyLeftSidedQuantale isStrictlyLeftSidedQuantale public

record IsAffineQuantale {c ℓ e} (Q : Quantale c ℓ e) : Set (suc (c ⊔ ℓ ⊔ e)) where
  open Quantale.Quantale Q public
  open BotTop Q

  field
    isUntialQuantale : IsUnitalQuantale Q

  open IsUnitalQuantale isUntialQuantale public

  field
    affine   : i ≈ ⊤

record AffineQuantale c ℓ e : Set (suc (c ⊔ ℓ ⊔ e)) where
  field
    Q : Quantale c ℓ e
    isAffineQuantale : IsAffineQuantale Q

  open IsAffineQuantale isAffineQuantale public

module MoreProperties {c ℓ e} (Q : Quantale c ℓ e) where

  open Quantale.Quantale Q public
  open Properties Q
  open BotTop Q
  open Inf-Poset Carrier _≤_ public

  idem+rside→strict :
      IsIdempotentQuantale Q
    → IsRightSidedQuantale Q
    → IsStrictlyRightSidedQuantale Q
  idem+rside→strict I RS =
    record
      { strictSidedʳ = λ {a} →
        antisym RS.sidedʳ
               (trans≤ (≤-respʳ-≈ (Eq.sym (I.isIdempotent a)) refl≤)
                       (*-congˡ (isUB (sup _) a tt)))
      }
      where module I  = IsIdempotentQuantale I
            module RS = IsRightSidedQuantale RS

  rsided→ab≤a : IsRightSidedQuantale Q → ∀ (a b : Carrier) → a * b ≤ a
  rsided→ab≤a RS a b = trans≤ (*-congˡ (⊤-max b)) RS.sidedʳ
      where module RS = IsRightSidedQuantale RS

record PreservesSups {c ℓ e} {A : CompleteJSL c ℓ e} {B : CompleteJSL c ℓ e} (f : CompleteJSL.Carrier A → CompleteJSL.Carrier B) : Set (suc (c ⊔ ℓ ⊔ e)) where
  module A = CompleteJSL A
  module B = CompleteJSL B

  field
    preserves-⋁ : ∀ {T : A.Carrier → Set (c ⊔ ℓ ⊔ e)}
                 → f (A.⋁ T) B.≈ B.⋁ (λ x → Σ[ p ∈ A.Carrier ] (T p × (f p B.≈ x)))

record Ragg  {c ℓ e} {A : CompleteJSL c ℓ e} {B : CompleteJSL c ℓ e} (f : CompleteJSL.Carrier A → CompleteJSL.Carrier B) : Set (suc (c ⊔ ℓ ⊔ e)) where
  module A = CompleteJSL A
  module B = CompleteJSL B

  field
    g : B.Carrier → A.Carrier
    t1 : ∀ {x y} → f x B.≤ y → x A.≤ g y
    t2 : ∀ {x y} → x A.≤ g y → f x B.≤ y

aft : ∀ {c ℓ e}
    → (A : CompleteJSL c ℓ e)
    → (B : CompleteJSL c ℓ e)
    → (f : CompleteJSL.Carrier A → CompleteJSL.Carrier B)
    → PreservesSups {A = A} {B = B} f
    → (∀ {x y} → CompleteJSL._≤_ A x y → CompleteJSL._≤_ B (f x) (f y))
    → Ragg {A = A} {B = B} f
aft {c} {ℓ} {e} A B f ps M =
  record
    { g = λ b → A.⋁ λ a → Lift (c ⊔ ℓ ⊔ e) (f a B.≤ b)
    ; t1 = λ {x} {y} fx≤y → A.isUB (A.sup _) x (lift fx≤y)
    ; t2 = λ {x} {y} x≤gy → B.trans (M x≤gy)
                                    (B.≤-respˡ-≈ (B.Eq.sym PS.preserves-⋁)
                                                 (B.isLUB (PS.B.sup _) y λ _ (_ , lift p , fpx) → B.≤-respˡ-≈ fpx p))
    } where module A = CompleteJSL A
            module B = CompleteJSL B
            module PS = PreservesSups ps
