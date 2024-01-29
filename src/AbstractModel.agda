module AbstractModel where

open import Type
open import Context Ty

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Semantics.Kripke.Frame

module Core (W : Set) (Acc : W → W → Set) (IF : IFrame W Acc) where

  open import Semantics.Presheaf.Base IF
  open import Semantics.Presheaf.CartesianClosure IF

  variable
    𝒫 𝒬 : Psh

  module _ (𝒫 : Psh) where
  
    open Psh 𝒫 renaming (Fam to P)

    record ◻'-Fam (w : W) : Set where
      constructor elem
      field
        fun     : {w' : W} → (r : Acc w w') → P w' 

    open ◻'-Fam renaming (fun to apply) public

    record _◻'-≋_ {w : W} (f g : ◻'-Fam w) : Set where
      constructor proof
      field
        pw : ∀ {w' : W} (r : Acc w w') → f .apply r ≋[ 𝒫 ] g .apply r
        
    ◻'_ : Psh
    ◻'_  = record
           { Fam           = ◻'-Fam
           ; _≋_           = _◻'-≋_
           ; ≋-equiv       = {!!}
           ; wk            = {!!}
           ; wk-pres-≋     = {!!}
           ; wk-pres-refl  = {!!}
           ; wk-pres-trans = {!!}
           }
