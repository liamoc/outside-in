open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Constraints( x : X) where
  open X(x)

  data Strata : Set where
    Flat : Strata
    Extended : Strata


  data Implication (knot : Set → Set)(n : Set) : Set where
    ∃_·_⊃_ : (v : ℕ) → QConstraint (n ⨁ v) → knot (n ⨁ v) → Implication knot n
  

  {- SYNTAX -}  
  data Constraint (n : Set) : Strata → Set where
    QC : ∀ {x} → QConstraint n → Constraint n x
    Imp : ∀ {x} → Implication (λ n → Constraint n x) n → Constraint n x
    _∧′_ : ∀ {x} → Constraint n x → Constraint n x → Constraint n x
    Ⅎ_ : ∀ {x} → Constraint (Ⓢ n) x → Constraint n Extended


  ε : ∀ {n}{x} → Constraint n x
  ε = QC (tautologyConstraint)

  _∼_ : ∀ {n}{x} → Type n → Type n → Constraint n x
  τ₁ ∼ τ₂ = QC (eqConstraint τ₁ τ₂)


  Ⅎ′_·_ : {n : Set}(v : ℕ) → Constraint (n ⨁ v) Extended → Constraint n Extended
  Ⅎ′ (suc n) · c = Ⅎ (Ⅎ′ n · c)
  Ⅎ′ zero · c = c

  infixl 6 Ⅎ′_·_ 

  toAE : {n : Set}{s : Strata} → Constraint n s → Constraint n Extended
  toAE (QC x) = QC x
  toAE (a ∧′ b) = toAE a ∧′ toAE b
  toAE (Imp (∃ n · Q ⊃ C)) = Imp (∃ n · Q ⊃ toAE C)
  toAE (Ⅎ c) = Ⅎ c

  infixl 6 Ⅎ_

  infixl 7 _∧′_

  {- INSTANCES -}
  private
    module PlusN-f n = Functor (Monad.is-functor (PlusN-is-monad {n}))
    module Ⓢ-f = Functor Ⓢ-is-functor
    module Type-f = Functor (type-is-functor)
    module QC-f = Functor (qconstraint-is-functor)

  private 
    fmap-c : ∀ {s}{a b} → (a → b) → Constraint a s → Constraint b s
    fmap-c f (QC x) = QC (QC-f.map f x)
    fmap-c f (C₁ ∧′ C₂) = (fmap-c f C₁) ∧′ (fmap-c f C₂)
    fmap-c f (Imp (∃ n · Q ⊃ C)) = Imp (∃ n · (QC-f.map (pn.map f) Q) ⊃ (fmap-c (pn.map f) C))
      where module pn = PlusN-f n 
    fmap-c f (Ⅎ C) = Ⅎ (fmap-c (Ⓢ-f.map f) C)
    fmap-c-id : ∀{s}{A : Set} {f : A → A} → isIdentity f → isIdentity (fmap-c {s} f)
    fmap-c-id {f = f} isid {QC x       } = cong QC (QC-f.identity isid)
    fmap-c-id {f = f} isid {Imp (∃ n · Q ⊃ C)} = cong Imp (cong₂ (∃_·_⊃_ n) (QC-f.identity (pn.identity isid)) (fmap-c-id (pn.identity isid)))
        where module pn = PlusN-f n
    fmap-c-id {f = f} isid {C₁ ∧′ C₂} = cong₂ _∧′_ (fmap-c-id isid) (fmap-c-id isid)
    fmap-c-id {f = f} isid {Ⅎ C    }  = cong Ⅎ_ (fmap-c-id (Ⓢ-f.identity isid))  
    fmap-c-comp : {s : Strata}{A B C : Set} {f : A → B} {g : B → C} {x : Constraint A s} 
                → fmap-c (g ∘ f) x ≡ fmap-c g (fmap-c f x)
    fmap-c-comp {x = QC x} = cong QC QC-f.composite
    fmap-c-comp {x = C₁ ∧′ C₂} = cong₂ _∧′_ (fmap-c-comp {x = C₁}) (fmap-c-comp {x = C₂})
    fmap-c-comp {x = Ⅎ C} = cong Ⅎ_ (trans (cong (λ t → fmap-c t C) (extensionality (λ x → Ⓢ-f.composite))) fmap-c-comp) 
    fmap-c-comp {x = Imp (∃ n · Q ⊃ C) } = cong Imp 
                                                (cong₂ (∃_·_⊃_ n) (trans (cong (λ t → QC-f.map t Q) 
                                                                               (extensionality (λ x → pn.composite))) 
                                                                         (QC-f.composite))
                                                                  (trans (cong (λ t → fmap-c t C) 
                                                                               (extensionality (λ x → pn.composite))) 
                                                                         (fmap-c-comp)))
      where module pn = PlusN-f n

  constraint-is-functor : ∀ {s : Strata} → Functor (λ n → Constraint n s)
  constraint-is-functor = record { map = fmap-c
                                 ; identity = fmap-c-id
                                 ; composite = fmap-c-comp
                                 }



