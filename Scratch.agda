module Scratch where
  open import OutsideIn.Prelude
  open import OutsideIn.X
  open import OutsideIn.Instantiations.Simple
  import OutsideIn

  data DCs : ℕ → Set where
    True : DCs 0
    False : DCs 0 

  data TCs : Set where
    BoolT : TCs


  open OutsideIn(Simple DCs)

  data ⊥ : Set where


  e : Expression ⊥ TCs _
  e = λ′ case Var (N zero) of 
                ( Con True  →′ Var (DC False)
                ∣ Con False →′ Var (DC True )
                ∣ esac
                )
  p : Program ⊥ TCs
  p = bind₁ e  
    , end

  
  Γ : Environment ⊥ TCs
  Γ (DC True) = DC∀′ 0 , 0 · SConstraint.ε ⇒ [] ⟶ BoolT 
  Γ (DC False) = DC∀′ 0 , 0 · SConstraint.ε ⇒ [] ⟶ BoolT 
  Γ (N ()) 

  test = go ax Γ (λ a b → true) p 
  test′ = generate′ Γ e -- (Var (BoolT) ⟶ Var (BoolT))