module PresheafProperties where

open import Function using (_∘_ ; id)
open import Data.Product 
open import Relation.Binary.PropositionalEquality

module ISet
  -- worlds
  (W : Set)
  -- accessibility relation
  (_≤_ : W → W → Set)
  -- relation is a preorder
  (refl-≤  : {w : W} → w ≤ w)
  (trans-≤ : {w w' w'' : W} → w ≤ w' → w' ≤ w'' → w ≤ w'')
  -- initial world
  (w0 : W)
  (init : {w : W} → w0 ≤ w)
  where

  infixr 19 _⇒ᵢ_
  infixr 19 _⇒ₚ_
  infixr 18 _→̇ᵢ_
  infixr 18 _→̇ₚ_
  
  -- a family of sets (called TYPE in the Coq impl.)
  ISet : Set₁
  ISet = (w : W) → Set

  -- a "raw" presheaf (i.e., without the laws)
  Psh : Set₁
  Psh = Σ ISet λ A → ∀ {w w' : W} → w ≤ w' → A w → A w'

  -- monotonicity of objects in Psh
  mon : (P : Psh) → ∀ {w w' : W} → w ≤ w' → proj₁ P w → proj₁ P w'
  mon = proj₂

  private
    variable 
      A B C : ISet
      X Y Z : Set
      P Q R : Psh

  -- morphisms in ISet
  _→̇ᵢ_ : ISet → ISet → Set
  A →̇ᵢ B = ∀ {w : W} → A w → B w

  -- exponentials in ISet
  _⇒ᵢ_ : ISet → ISet → ISet
  A ⇒ᵢ B = λ w → A w → B w

  -- products in ISet
  _×ᵢ_ : ISet → ISet → ISet
  A ×ᵢ B = λ w → A w × B w

  -- morphisms in Psh
  _→̇ₚ_ : Psh → Psh → Set
  P →̇ₚ Q = proj₁ P →̇ᵢ proj₁ Q

  -- products in Psh
  _×ₚ_ : Psh → Psh → Psh
  P ×ₚ Q = proj₁ P ×ᵢ proj₁ Q , λ { wRw' (p , q)  → mon P wRw' p , mon Q wRw' q }
  
  --
  -- Functors of interest
  --
  
  𝒰 : Psh → ISet
  𝒰 = proj₁
  
  𝒰₁ : (f : P →̇ₚ Q) → 𝒰 P →̇ᵢ 𝒰 Q
  𝒰₁ f = f

  ℱ : ISet → Psh
  ℱ A = (λ w → Σ W (λ w' → w' ≤ w × A w')) , λ { wRw' (v , vRw , Av) → v , (trans-≤ vRw wRw' , Av) }

  ℱᵢ : (f : A →̇ᵢ B) → ℱ A →̇ₚ ℱ B
  ℱᵢ f (w , wRw' , a)= w , wRw' , f a
  
  𝒞 : ISet → Psh
  𝒞 A = (λ w → ∀ {w' : W} → w ≤ w' → A w') , λ wRw' f w'Rw'' → f (trans-≤ wRw' w'Rw'')

  𝒞₁ : (f : A →̇ᵢ B) → 𝒞 A →̇ₚ 𝒞 B
  𝒞₁ f g wRw' = f (g wRw')

  -- known: ℱ ⊣ 𝒰 ⊣ 𝒞

  Con : Set → ISet
  Con X = λ _ → X

  Con₁ : (f : X → Y) → Con X →̇ᵢ Con Y
  Con₁ f {_} = f
  
  Pi : ISet → Set
  Pi X = ∀ {w : W} → X w

  Pi₁ : (f : A →̇ᵢ B) → Pi A → Pi B
  Pi₁ f a = f a

  Si : ISet → Set
  Si X = Σ W X

  Siᵢ : (f : A →̇ᵢ B) → Si A → Si B
  Siᵢ f (w , a) = w , (f a)

  -- known: Si ⊣ Con ⊣ Pi 

  GS : Psh → Set
  GS (A , _) = A w0

  GS₁ : (P →̇ₚ Q) → GS P → GS Q
  GS₁ f = f

  -- known GS₁ ∘ 𝒞 ≅ Pi (when w0 is initial)
  
  --
  -- A comonad ◻ on ISet
  --
  
  ◻_ : ISet → ISet
  ◻_ = 𝒰 ∘ 𝒞
  
  ◻ᵢ_ : (f : A →̇ᵢ B) → ◻ A →̇ᵢ ◻ B
  ◻ᵢ_ {A} {B} = 𝒰₁ {𝒞 A} {𝒞 B} ∘ 𝒞₁
  
  ε◻ : ◻ A →̇ᵢ A
  ε◻ f = f refl-≤

  ν◻ : ◻ A →̇ᵢ ◻ ◻ A
  ν◻ f wRw' w'Rw'' = f (trans-≤ wRw' w'Rw'')

  --
  -- A monad ◆ on Set
  --

  ◆_ : Set → Set
  ◆_ = Pi ∘ ◻_ ∘ Con

  η◆ : X → ◆ X
  η◆ x _wRw' = x

  μ◆ : ◆ (◆ X) → ◆ X
  μ◆ ddx wRw' = ddx wRw' wRw'

  --
  -- Necessitation and denecessitation
  --
  
  denec : Pi (◻ A) → Pi A
  denec = Pi₁ ε◻

  -- what is going on here?
  nec : Pi A → Pi (◻ A)
  nec {A} va {w} {w'} wRw' = η◆ {X = A w'} va wRw'

  -- TODO: demystify the ◆ monad and derive this
  -- equality from properties of denec and nec
  denec∘nec-is-id : denec ∘ nec ≡ id {_} {Pi A}
  denec∘nec-is-id = refl

  --
  -- Corollaries
  --
  
  _⇒ₚ_ : Psh → Psh → Psh
  P ⇒ₚ Q = (◻ (𝒰 P ⇒ᵢ 𝒰 Q)) , λ wRw' f w'Rw'' pAtw'' → f (trans-≤ wRw' w'Rw'') pAtw''
  
  fromExp : Pi (𝒰 (P ⇒ₚ Q)) → Pi (𝒰 P ⇒ᵢ 𝒰 Q)
  fromExp = denec
  
  toExp : Pi (𝒰 P ⇒ᵢ 𝒰 Q) → Pi (𝒰 (P ⇒ₚ Q))
  toExp = nec

  _ : fromExp {P} {Q} ∘ toExp {P} {Q} ≡ id
  _ = denec∘nec-is-id


  
