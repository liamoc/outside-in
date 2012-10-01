open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Prenexer(x : X) where  
  import OutsideIn.Constraints as C
  import OutsideIn.Expressions as E
  open E(x)
  open C(x)
  open X(x)
  private module PlusN-m n        = Monad (PlusN-is-monad {n})
          module PlusN-f n        = Functor (Monad.is-functor (PlusN-is-monad {n}))
          module Constraint-f {s} = Functor (constraint-is-functor {s})
          module QC-f             = Functor (qconstraint-is-functor)


  data _prenex:_,_ {n : Set} : Constraint n Extended → (m : ℕ) → Constraint (n ⨁ m) Flat → Set where
    PN-QC : ∀ {x} → QC x prenex: 0 , QC x
    PN-∧  : ∀ {a b}{na nb}{a′}{b′} → a prenex: na , a′ → b prenex: nb , b′ 
          → (a ∧′ b) prenex: (na + nb) , 
                                               (Constraint-f.map ((subst id (sym (PlusN-collect {n}{na}{nb}))) ∘ PlusN-m.unit nb) a′
                                             ∧′ Constraint-f.map ((subst id (sym (PlusN-collect {n}{na}{nb})))  ∘ PlusN-f.map nb (PlusN-m.unit na)) b′)
    PN-Imp : ∀ {q}{c}{m}{c′} 
           → c prenex: m , c′ 
           → Imp′ q c prenex: 0 , Imp (∃ m · q ⊃ c′)
    PN-Ext  : ∀ {x}{n}{x′} → x prenex: n , x′ → (Ⅎ_ x) prenex: suc n , x′


  prenex : ∀ {n} → (C : Constraint n Extended) → ∃ (λ m → ∃ (λ C′ → C prenex: m , C′))
  prenex (QC x) = _ , _ , PN-QC
  prenex {n} (a ∧′ b) with prenex a | prenex b
  ... | na , a′ , p₁ | nb , b′ , p₂ = _ , _ , PN-∧ p₁ p₂
  prenex {n} (Imp′ q c) with prenex c
  ... | m , c′ , p = _ , _ , PN-Imp p 
  prenex (Ⅎ_ x) with prenex x
  ... | n , x′ , p = _ , _ , PN-Ext  p 