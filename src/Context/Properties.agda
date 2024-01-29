{-# OPTIONS --safe --without-K #-}
module Context.Properties where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
  
open import Type using (Ty)
open import Context.Base Ty

private
  variable
    a b c d : Ty
  
⊆-refl-unit-left : (w : Γ' ⊆ Γ) → ⊆-refl ∙ w ≡ w
⊆-refl-unit-left base      = refl
⊆-refl-unit-left (drop w)  = cong drop (⊆-refl-unit-left w)
⊆-refl-unit-left (keep w)  = cong keep (⊆-refl-unit-left w)

-- weakening composition obeys the right identity law
⊆-refl-unit-right : (w : Γ' ⊆ Γ) → w ∙ ⊆-refl ≡ w
⊆-refl-unit-right base      = refl
⊆-refl-unit-right (drop w)  = cong drop (⊆-refl-unit-right w)
⊆-refl-unit-right (keep w)  = cong keep (⊆-refl-unit-right w)

-- weakening composition is associative
∙-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊆ Γ3) (w2 : Γ3 ⊆ Γ2) → (w1 : Γ2 ⊆ Γ1)
  → (w3 ∙ w2) ∙ w1 ≡ w3 ∙ (w2 ∙ w1)
∙-assoc w3         w2         base       = refl
∙-assoc w3         w2         (drop w1)  = cong drop (∙-assoc w3 w2 w1)
∙-assoc w3         (drop w2)  (keep w1)  = cong drop (∙-assoc w3 w2 w1)
∙-assoc (drop w3)  (keep w2)  (keep w1)  = cong drop (∙-assoc w3 w2 w1)
∙-assoc (keep w3)  (keep w2)  (keep w1)  = cong keep (∙-assoc w3 w2 w1)

wkVar-pres-⊆-refl : (x : Var Γ a) → wkVar ⊆-refl x ≡ x
wkVar-pres-⊆-refl v0       = refl
wkVar-pres-⊆-refl (succ x) = cong succ (wkVar-pres-⊆-refl x)

wkVar-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (x : Var Γ a)
  → wkVar w' (wkVar w x) ≡ wkVar (w ∙ w') x
wkVar-pres-⊆-trans (drop w) (drop w') zero     = cong succ (wkVar-pres-⊆-trans (drop w) w' zero)
wkVar-pres-⊆-trans (drop w) (keep w') zero     = cong succ (wkVar-pres-⊆-trans w w' zero)
wkVar-pres-⊆-trans (keep w) (drop w') zero     = cong succ (wkVar-pres-⊆-trans (keep w) w' zero)
wkVar-pres-⊆-trans (keep w) (keep w') zero     = refl
wkVar-pres-⊆-trans (drop w) (drop w') (succ x) = cong succ (wkVar-pres-⊆-trans (drop w) w' (succ x))
wkVar-pres-⊆-trans (drop w) (keep w') (succ x) = cong succ (wkVar-pres-⊆-trans w w' (succ x))
wkVar-pres-⊆-trans (keep w) (drop w') (succ x) = cong succ (wkVar-pres-⊆-trans (keep w) w' (succ x))
wkVar-pres-⊆-trans (keep w) (keep w') (succ x) = cong succ (wkVar-pres-⊆-trans w w' x)

freshWk-natural : (w : Γ ⊆ Γ') → w ∙ freshWk[ Γ' , a ] ≡ freshWk[ Γ , a ] ∙ keep w
freshWk-natural w = cong drop (≡-trans (⊆-refl-unit-right w) (≡-sym (⊆-refl-unit-left w)))
