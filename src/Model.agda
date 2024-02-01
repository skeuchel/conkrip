module Model where

open import Type
open import Context Ty

open import Data.List
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Function using (id ; _∘_)

data Val (Γ : Ctx) : Ty → Set where
  var : Var Γ a → Val Γ a
  true false : Val Γ bool
  -- etc.

wkVal : Γ ⊆ Γ' → Val Γ a → Val Γ' a
wkVal w (var x) = var (wkVar w x)
wkVal w true    = true
wkVal w false   = false

open import Substitution Ty Val var wkVal

data PredApp (Γ : Ctx) : Set where
  𝒫_  : Val Γ a → PredApp Γ 
  _＝_ : Val Γ a → Val Γ a → PredApp Γ
  -- etc.

data Form : Ctx → Set where
  Uni Bot : Form Γ
  _∧_     : PredApp Γ → Form Γ → Form Γ
  ∃'_ ∀'_ : Form (Γ `, a) → Form Γ
  -- etc.

-- "Path condition"
Con : Ctx → Set
Con Γ = List (PredApp Γ)

-- pure laziness
postulate
  substCon : Con Γ → Sub Δ Γ → Con Δ

-- an interface to the model (defined in a module below)
module ISet
  -- worlds
  (W : Set)
  -- accessibility relation
  (Acc : W → W → Set)
  -- retrieve a context from worlds
  (wCtx : W → Ctx)
  -- relation is a preorder
  (refl-Acc : {w : W} → Acc w w)
  (trans-Acc : {w w' w'' : W} → Acc w w' → Acc w' w'' → Acc w w'')
  where

  -- a family of sets (called TYPE in the Coq impl.)
  ISet : Set₁
  ISet = (w : W) → Set

  private
    variable 
      A B C : ISet
      
  -- validity (can also be read as "universal")
  ⊨ : ISet → Set
  ⊨ A = ∀ {w : W} → A w

  infixr 19 _⟶_
  infixr 19 _⇒_
  infixr 18 _→̇_

  -- map at a world
  _⟶_ : ISet → ISet → ISet
  A ⟶ B = λ w → A w → B w

  -- box modality
  ◻_ : ISet → ISet
  ◻ A = λ w → ∀ {w' : W} → Acc w w' → A w' 

  -- natural transformation
  _→̇_ : ISet → ISet → Set
  A →̇ B = ∀ {w : W} → A w → B w

  -- exponential (or "Kripke function space")
  _⇒_ : ISet → ISet → ISet
  A ⇒ B = λ w → ∀ {w' : W} → Acc w w' → A w' → B w'

  -- product
  _×'_ : ISet → ISet → ISet
  A ×' B = λ w → A w × B w

  -- demonstrate equivalences between using a combination
  -- of (⊨, ⟶, ◻) vs. a combination of (⊨, ⟶̇, ⇒)
  -- to define operations in the model.
  module _ where

    -- a valid map (i.e., map at an arbitrary world)
    -- is a natural transformation
    ⊨⟶≅→̇ : ⊨ (A ⟶ B) ≡ (A →̇ B)
    ⊨⟶≅→̇ = refl

    -- a boxed map (i.e., map at all future worlds)
    -- is an exponential
    ◻⟶≅⇒ : ◻ (A ⟶ B) ≡ (A ⇒ B)
    ◻⟶≅⇒ = refl

    --
    -- axiom T can be presented in two equivalent ways
    --
    
    -- 1. as a valid map 
    axT : ⊨ (◻ A ⟶ A)
    axT f = f refl-Acc
    
    -- 2. as a natural transformation
    axT' : ◻ A →̇ A
    axT' = axT

    --
    -- a "higher-order" axiom T can be presented in two equivalent ways
    --
    
    -- 1. as a valid map
    hoAxT : ⊨ (◻ (◻ A ⟶ A))
    hoAxT wRw' g = g refl-Acc

    -- as a valid exponential
    hoAxT' : ⊨ (◻ A ⇒ A)
    hoAxT' = hoAxT

  --
  -- ⊨ is functorial (from ISet to Set)
  --
  
  ⊨-map : A →̇ B → ⊨ A → ⊨ B
  ⊨-map f p = f p

  ⊨-map-pres-id : ⊨-map {A} id ≡ id
  ⊨-map-pres-id = refl

  ⊨-map-pres-∘ : (f : A →̇ B) (g : B →̇ C) → ⊨-map {B} g ∘ ⊨-map f ≡ ⊨-map (g ∘ f) 
  ⊨-map-pres-∘ _ _ = refl

  --
  -- domain specific families
  --
  
  -- indexed set of values
  Valᵢ : Ty → ISet
  Valᵢ a w = Val (wCtx w) a

  -- indexed set of deeply-embedded propositions
  Formᵢ : ISet
  Formᵢ w = Form (wCtx w)

  -- Spure as in the paper 
  Sp : ISet → ISet
  Sp A = ◻ (A ⟶ Formᵢ) ⟶ Formᵢ

  -- Spure variant defined by _the_ continuation monad (with Formᵢ result)
  Sp' : ISet → ISet
  Sp' A = (A ⇒ Formᵢ) ⇒ Formᵢ

  -- investigates the relationship between the types Sp and Sp'
  module _ where

    -- since `Sp' A` is merely a special case of exponentials
    -- and `Sp A` is merely a special case of maps by defn.,
    -- we may study exponentials vs maps instead of `Sp' A` vs. `Sp A`

    -- exponentials yield maps at (respective) worlds 
    ⇒-to-⟶ : (A ⇒ B) →̇ (A ⟶ B)
    ⇒-to-⟶ {w = w} f = f {w} refl-Acc

    -- a valid exponential yields a valid map
    fromExp : ⊨ (A ⇒ B) → ⊨ (A ⟶ B)
    fromExp = ⊨-map ⇒-to-⟶

    -- a valid map yields a valid exponential
    toExp : ⊨ (A ⟶ B) → ⊨ (A ⇒ B)
    toExp p {w} {w'} wRw' f = p {w'} f

    -- fromExp is a retraction (or left inverse) of toExp
    toAndFromExp-is-id : fromExp ∘ toExp ≡ id {_} {⊨ (A ⟶ B)}
    toAndFromExp-is-id = refl

    -- this doesn't seem to hold; why?
    --fromAndtoExp-is-id : toExp ∘ fromExp ≡ id {_} {⊨ (A ⇒ B)}
    --fromAndtoExp-is-id = {!!}

    --
    -- observe the following corollary
    --
    
    fromSp' = fromExp
    toSp'   = toExp

    -- corollary: we can go from `⊨ (Sp A)` to `⊨ (Sp' A)` and back without loss
    toAndFromSp'-is-id : fromSp' ∘ toSp' ≡ id {_} {⊨ (Sp A)}
    toAndFromSp'-is-id = toAndFromExp-is-id

  -- presheaves as a submodel of families of sets
  module Psh
    -- require proofs of monotonicity for domain-specific families
    (monVal  : {a : Ty} {w w' : W} → Acc w w' → Val (wCtx w) a → Val (wCtx w') a)
    (monForm : {w w' : W} → Acc w w' → Form (wCtx w) → Form (wCtx w'))
    where

    -- a "raw" presheaf (i.e., without the laws)
    Psh : Set₁
    Psh = Σ ISet λ A → ∀ {w w' : W} → Acc w w' → A w → A w'   

    -- extract the underlying family of sets
    [_]ᵢ : Psh → ISet
    [_]ᵢ = proj₁

    -- extract the "monotonicity" proof
    mon : (P : Psh) → ∀ {w w' : W} → Acc w w' → [ P ]ᵢ w → [ P ]ᵢ w' 
    mon = proj₂

    --
    -- domain specific presheaves
    --
  
    --  presheah of values
    Valₚ : Ty → Psh
    Valₚ a = (Valᵢ a) , monVal

    -- presheaf of deepply-embedded propositions 
    Formₚ : Psh
    Formₚ = Formᵢ , monForm  

    --
    -- Exponentials and the Sp' monad
    --
    
    -- presheaf exponentials, functoriality and strength of Sp'
    -- (this module asks for two extra arguments for every function in it) 
    module _ (Xₚ Yₚ : Psh) where
    
      -- local definitions to reduce clutter
      private
        X     = [ Xₚ ]ᵢ
        monX  = mon Xₚ
        
        Y    = [ Yₚ ]ᵢ
        monY = mon Yₚ

      -- monotonicity for exponentials
      mon⇒ : ∀ {w w' : W} → Acc w w' → (X ⇒ Y) w → (X ⇒ Y) w'
      mon⇒ wRw' f = λ w'Rw'' → f (trans-Acc wRw' w'Rw'')

      -- presheaf exponential
      _⇒ₚ_ : Psh
      _⇒ₚ_ = X ⇒ Y , mon⇒ 

      -- functor map of Sp'
      fmapSp' : (X →̇ Y) → Sp' X →̇  Sp' Y
      fmapSp' f g wRw' h = g wRw' (λ w'Rw'' x → h w'Rw'' (f x))

      -- strength of the functor Sp'
      strengthSp' : (X ×' Sp' Y) →̇ Sp' (X ×' Y)
      strengthSp' (x , f) wRw' g = f wRw' (λ w'Rw'' y → g w'Rw'' (monX (trans-Acc wRw' w'Rw'') x , y))

    -- (explicitly) define the functorial action of Sp'
    Sp'-functorial : Psh → Psh
    Sp'-functorial Aₚ@(Aᵢ , monA) = (Sp' Aᵢ) , mon⇒ (Aₚ ⇒ₚ Formₚ) Formₚ

    -- Sp' defines a monad on presheaves
    module _ (Xₚ : Psh) where
    
      -- local definitions to reduce clutter
      private
        X     = [ Xₚ ]ᵢ
        monX  = mon Xₚ

      -- Sp' has a return
      returnSp' : X →̇ Sp' X
      returnSp' a wRw' f = f refl-Acc (monX wRw' a)

      -- Sp' has a join
      joinSp' : Sp' (Sp' X) →̇ Sp' X
      joinSp' f wRw' g = f wRw' (λ w'Rw'' h → h refl-Acc (mon⇒ Xₚ Formₚ w'Rw'' g))

-- The concrete model
module Core
  (_⊢_ : {Γ : Ctx} → Con Γ → Con Γ → Set)
  (refl-⊢ : {Γ : Ctx} {c : Con Γ} → c ⊢ c)
  where

  open import Data.Product

  W : Set
  W = Σ Ctx Con

  wCtx = proj₁
  wCon = proj₂
  
  Acc : W → W → Set
  Acc (Δ₁ , C₁) (Δ₂ , C₂) = Σ (Sub Δ₂ Δ₁) (λ δ → C₂ ⊢ substCon C₁ δ)

  -- pure laziness
  postulate
    refl-Acc  : {w : W} → Acc w w
    trans-Acc : {w w' w'' : W} → Acc w w' → Acc w' w'' → Acc w w''
    
  open ISet W Acc wCtx refl-Acc trans-Acc

  𝟙 : ISet
  𝟙 _ = ⊤
  
  demonic : 𝟙 →̇ Sp' (Valᵢ a)
  demonic {a = a} _ {w' = w'} wRw' post = ∀' (post {u} w'Ru (var zero))
    where
      -- a future world of w'
      u : W
      u = (wCtx w' `, a) ,  substCon (wCon w') (dropₛ idₛ)
      
      w'Ru : Acc w' u
      w'Ru = dropₛ idₛ , refl-⊢

  -- angelic : 𝟙 →̇ Sp' (𝕍 a)
  -- _⊕_ : Sp' (𝕍 a) ×' Sp' (𝕍 a) →̇ Sp' (𝕍 a)
  -- etc.,
