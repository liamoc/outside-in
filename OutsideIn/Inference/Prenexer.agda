open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Prenexer(x : X) where  
  open import Data.Product
  import OutsideIn.Constraints as C
  import OutsideIn.Expressions as E
  open E(x)
  open C(x)
  open X(x)
  private module PlusN-m n        = Monad (PlusN-is-monad {n})
          module PlusN-f n        = Functor (Monad.is-functor (PlusN-is-monad {n}))
          module Constraint-f {s} = Functor (constraint-is-functor {s})
          module QC-f             = Functor (qconstraint-is-functor) 
  prenex : ∀ {n} → Constraint n Extended → ∃ (λ m → Constraint (n ⨁ m) Flat)
  prenex (Q-c x) = 0 , Q-c x
  prenex {n} (a ∧′ b) with prenex a | prenex b
  ... | na , a′ | nb , b′ = na + nb , subst (λ x → Constraint x Flat) (sym (PlusN-collect {n}{na}{nb})) 
                                            (Constraint-f.map pnb.unit a′ ∧′ Constraint-f.map (pnb-f.map pna.unit) b′)
     where module pna = PlusN-m na
           module pnb = PlusN-m nb
           module pnb-f = PlusN-f nb
  prenex {n} (∃ v · q ⊃ c) with prenex {n ⨁ v} c
  ... | m , c′ = 0 , ∃ v + m · subst QConstraint (sym (PlusN-collect {n}{v}{m})) (QC-f.map pm.unit q) 
                             ⊃ subst (λ x → Constraint x Flat) (sym (PlusN-collect {n}{v}{m})) c′
     where module pm = PlusN-m m
  prenex (Ⅎ_ {Extended} x) with prenex x
  ... | n , x′ = suc n , x′
  prenex (Ⅎ_ {Flat} x) = 1 , x
--  prenex (Ⅎ_ {Flat} x) = 1 , toAF x
   