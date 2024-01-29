{-# OPTIONS --safe --without-K #-}
module Type where

data Ty : Set where
  bool  : Ty
  other : Ty
  -- etc.,

variable
  a b c d : Ty
