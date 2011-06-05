{-# OPTIONS --universe-polymorphism #-}
module RevRev where

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality 
  as P using (_≡_; refl; cong)

ReverseReverseId : ∀ {a} {A : Set a} (xs : List A) -> 
                   reverse (reverse xs) ≡ xs
ReverseReverseId [] = refl
ReverseReverseId (x ∷ xs) = 
  begin
    reverse (reverse (x ∷ xs)) 
      ≡⟨ cong (λ zs → reverse zs) (unfold-reverse x xs) ⟩ 
    
      _≡⟨_⟩_ {!!}
    x ∷ xs
  ∎
  where open P.≡-Reasoning
