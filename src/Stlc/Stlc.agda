module Stlc where

import Data.Tree.AVL

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open Data.Tree.AVL <-strictTotalOrder-≈ using (Tree; const; insert; lookup)

data Ty : Set where
  bool : Ty
  func : Ty -> Ty -> Ty

Ctx : Set
Ctx = Tree (const Ty)

data Exp : Set where
  var : String -> Exp
  app : Exp -> Exp -> Exp
  abs : String -> Exp -> Exp
  true false : Exp
  ift : Exp -> Exp -> Exp -> Exp

_∋_∶_ : Ctx -> String -> Ty -> Set
Γ ∋ x ∶ τ = lookup x Γ ≡ just τ

data _⊢_∶_ (Γ : Ctx) : Exp -> Ty -> Set where
  ty-var : ∀ {x τ} →
    Γ ∋ x ∶ τ →
    Γ ⊢ var x ∶ τ
  ty-app : ∀ {e₁ e₂ τ₁ τ₂} →
    Γ ⊢ e₁ ∶ func τ₁ τ₂ →
    Γ ⊢ e₂ ∶ τ₁ →
    Γ ⊢ app e₁ e₂ ∶ τ₂
  ty-abs : ∀ {x τ₁ τ₂ e} →
    insert x τ₁ Γ ⊢ e ∶ τ₂ →
    Γ ⊢ abs x e ∶ func τ₁ τ₂
  ty-true :
    Γ ⊢ true ∶ bool
  ty-false :
    Γ ⊢ false ∶ bool
  ty-ift : ∀ {e₁ e₂ e₃ τ} →
    Γ ⊢ e₁ ∶ bool →
    Γ ⊢ e₂ ∶ τ →
    Γ ⊢ e₃ ∶ τ →
    Γ ⊢ ift e₁ e₂ e₃ ∶ τ

-- Shallowly embedded constraints
module Shallow where

  data Constraint : Set where
    True False : Constraint
    And : Constraint -> Constraint -> Constraint
    Equal : Ty -> Ty -> Constraint
    Exist : (Ty -> Constraint) -> Constraint

  ⟦_⟧ : Constraint -> Set
  ⟦ True        ⟧ = ⊤
  ⟦ False       ⟧ = ⊥
  ⟦ And C₁ C₂   ⟧ = ⟦ C₁ ⟧ × ⟦ C₂ ⟧
  ⟦ Equal τ₁ τ₂ ⟧ = τ₁ ≡ τ₂
  ⟦ Exist f     ⟧ = Σ Ty λ τ → ⟦ f τ ⟧

  gen-var : Maybe Ty -> Ty -> Constraint
  gen-var (just τ') τ = Equal τ' τ
  gen-var nothing τ = False

  gen : Ctx -> Exp -> Ty -> Constraint
  gen Γ (var x) τ = gen-var (lookup x Γ) τ
  gen Γ (app e₁ e₂) τ₂ = Exist λ τ₁ → And (gen Γ e₁ (func τ₁ τ₂)) (gen Γ e₂ τ₁)
  gen Γ (abs x e) τ = Exist λ τ₁ → Exist λ τ₂ → And (Equal (func τ₁ τ₂) τ) (gen (insert x τ₁ Γ) e τ₂)
  gen Γ true τ = Equal τ bool
  gen Γ false τ = Equal τ bool
  gen Γ (ift e₁ e₂ e₃) τ = And (gen Γ e₁ bool) (And (gen Γ e₂ τ) (gen Γ e₃ τ))

  sound-var : ∀ {m τ} → ⟦ gen-var m τ ⟧ → m ≡ just τ
  sound-var {m = just x} = cong just

  sound : ∀ {Γ} e {τ} → ⟦ gen Γ e τ ⟧ → Γ ⊢ e ∶ τ
  sound (var x)        p                     =  ty-var (sound-var p)
  sound (app e₁ e₂)    (τ₁ , p₁ , p₂)        =  ty-app (sound e₁ p₁) (sound e₂ p₂)
  sound (abs x e)      (τ₁ , τ₂ , refl , p)  =  ty-abs (sound e p)
  sound true           refl                  =  ty-true
  sound false          refl                  =  ty-false
  sound (ift e₁ e₂ e₃) (p₁ , p₂ , p₃)        =  ty-ift (sound e₁ p₁) (sound e₂ p₂) (sound e₃ p₃)

  complete-var : ∀ {m τ} → m ≡ just τ → ⟦ gen-var m τ ⟧
  complete-var {m = just τ'} refl = refl
  complete-var {m = nothing} ()

  complete : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → ⟦ gen Γ e τ ⟧
  complete (ty-var p)        = complete-var p
  complete (ty-app p₁ p₂)    = _ , complete p₁ , complete p₂
  complete (ty-abs p)        = _ , _ , refl , complete p
  complete ty-true           = refl
  complete ty-false          = refl
  complete (ty-ift p₁ p₂ p₃) = complete p₁ , complete p₂ , complete p₃

-- Deeply embedded constraints
module Deep where

  data OTy (w : ℕ) : Set where
    evar : Fin w -> OTy w
    bool : OTy w
    func : OTy w -> OTy w -> OTy w

  Assignment : ℕ -> Set
  Assignment = Vec Ty

  _[_] : ∀ {w} → OTy w -> Assignment w -> Ty
  evar α     [ ι ] = Data.Vec.lookup ι α
  bool       [ ι ] = bool
  func τ₁ τ₂ [ ι ] = func (τ₁ [ ι ]) (τ₂ [ ι ])

  data Constraint (w : ℕ) : Set where
    True False : Constraint w
    And : Constraint w -> Constraint w -> Constraint w
    Equal : OTy w -> OTy w -> Constraint w
    Exist : Constraint (suc w) -> Constraint w

  Pred : ℕ -> Set₁
  Pred n = Assignment n -> Set

  ⟦_⟧ : ∀ {w} → Constraint w -> Pred w
  ⟦ True        ⟧ ι = ⊤
  ⟦ False       ⟧ ι = ⊥
  ⟦ And C₁ C₂   ⟧ ι = ⟦ C₁ ⟧ ι × ⟦ C₂ ⟧ ι
  ⟦ Equal τ₁ τ₂ ⟧ ι = τ₁ [ ι ] ≡ τ₂ [ ι ]
  ⟦ Exist C     ⟧ ι = Σ Ty λ τ → ⟦ C ⟧ (τ ∷ ι)

  OCtx : ℕ -> Set
  OCtx w = Tree (const (OTy w))

  gen-var : ∀ {w} → Maybe (OTy w) -> OTy w -> Constraint w
  gen-var (just τ') τ = Equal τ' τ
  gen-var nothing τ   = False

  wkΓ : ∀ {w} → OCtx w → OCtx (suc w)
  wkΓ = {!!}

  wkτ : ∀ {w} → OTy w -> OTy (suc w)
  wkτ = {!!}

  gen : Exp -> ∀ {w} → OCtx w -> OTy w -> Constraint w
  gen (var x)        Γ τ  = gen-var (lookup x Γ) τ
  gen (app e₁ e₂)    Γ τ₂ = let τ₁ = evar zero in
                            Exist (And (gen e₁ (wkΓ Γ) (func τ₁ (wkτ τ₂))) (gen e₂ (wkΓ Γ) τ₁))
  gen (abs x e)      Γ τ  = Exist (Exist
                            let τ₁ = evar (suc zero)
                                τ₂ = evar zero
                            in And (Equal (func τ₁ τ₂) (wkτ (wkτ τ)))
                                   (gen e (insert x τ₁ (wkΓ (wkΓ Γ))) τ₂))
  gen true           Γ τ  = Equal τ bool
  gen false          Γ τ  = Equal τ bool
  gen (ift e₁ e₂ e₃) Γ τ  = And (gen e₁ Γ bool) (And (gen e₂ Γ τ) (gen e₃ Γ τ))
