open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Constraints( x : X) where
  open X(x)
--  open import OutsideIn.Types

  data Strata : Set where
    Flat : Strata
    Extended : Strata

  

  {- SYNTAX -}  
  data Constraint (n : Set) : Strata → Set where
    Q-c : ∀ {x} → QConstraint n → Constraint n x
--    ε : ∀ {x} → Constraint n x

--    _∼_ : ∀ {x} → Type n → Type n → Constraint n x
    _∧′_ : ∀ {x} → Constraint n x → Constraint n x → Constraint n x
    ∃_·_⊃_ : ∀ {x} → (v : ℕ) →  QConstraint (n ⨁ v) → Constraint (n ⨁ v) x → Constraint n x
    Ⅎ_ : ∀ {x} → Constraint (Ⓢ n) x → Constraint n (Extended)


  ε : ∀ {n}{x} → Constraint n x
  ε = Q-c (tautologyConstraint)

  _∼_ : ∀ {n}{x} → Type n → Type n → Constraint n x
  τ₁ ∼ τ₂ = Q-c (eqConstraint τ₁ τ₂)


  Ⅎ′_·_ : {n : Set}(v : ℕ) → Constraint (n ⨁ v) Extended → Constraint n Extended
  Ⅎ′ (suc n) · c = Ⅎ (Ⅎ′ n · c)
  Ⅎ′ zero · c = c

  infixl 6 Ⅎ′_·_ 

  toAE : {n : Set}{s : Strata} → Constraint n s → Constraint n Extended
--  toAE ε = ε
  toAE (Q-c x) = Q-c x
  toAE (a ∧′ b) = toAE a ∧′ toAE b
  --toAE (t ∼ u)  = t ∼ u
  toAE (∃ n · Q ⊃ C) = ∃ n · Q ⊃ toAE C
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
    fmap-c f (Q-c x) = Q-c (QC-f.map f x)
    fmap-c f (C₁ ∧′ C₂) = (fmap-c f C₁) ∧′ (fmap-c f C₂)
    fmap-c f (∃ n · Q ⊃ C) = ∃ n · (QC-f.map (pn.map f) Q) ⊃ (fmap-c (pn.map f) C) 
      where module pn = PlusN-f n 
    fmap-c f (Ⅎ C) = Ⅎ (fmap-c (Ⓢ-f.map f) C)
    fmap-c-id : ∀{s}{A : Set} {f : A → A} → isIdentity f → isIdentity (fmap-c {s} f)
    fmap-c-id {f = f} isid {Q-c x       } = cong Q-c (QC-f.identity isid)
    fmap-c-id {f = f} isid {∃ n · Q ⊃ C } = cong₂ (∃_·_⊃_ n) (QC-f.identity (pn.identity isid)) (fmap-c-id (pn.identity isid))
        where module pn = PlusN-f n
    fmap-c-id {f = f} isid {C₁ ∧′ C₂} = cong₂ _∧′_ (fmap-c-id isid) (fmap-c-id isid)
    --fmap-c-id {f = f} isid {α  ∼  β } = cong₂ _∼_  (Type-f.identity isid) (Type-f.identity isid)
    fmap-c-id {f = f} isid {Ⅎ C    }  = cong Ⅎ_ (fmap-c-id (Ⓢ-f.identity isid))  
    fmap-c-comp : {s : Strata}{A B C : Set} {f : A → B} {g : B → C} {x : Constraint A s} 
                → fmap-c (g ∘ f) x ≡ fmap-c g (fmap-c f x)
    fmap-c-comp {x = Q-c x} = cong Q-c QC-f.composite
    fmap-c-comp {x = C₁ ∧′ C₂} = cong₂ _∧′_ (fmap-c-comp {x = C₁}) (fmap-c-comp {x = C₂})
    --fmap-c-comp {x = α  ∼  β } = cong₂ _∼_ Type-f.composite Type-f.composite
    fmap-c-comp {x = Ⅎ C} = cong Ⅎ_ (trans (cong (λ t → fmap-c t C) (extensionality (λ x → Ⓢ-f.composite))) fmap-c-comp) 
    fmap-c-comp {x = ∃ n · Q ⊃ C } = cong₂ (∃_·_⊃_ n) (trans (cong (λ t → QC-f.map t Q) (extensionality (λ x → pn.composite))) (QC-f.composite))
                                                      (trans (cong (λ t → fmap-c t C) (extensionality (λ x → pn.composite))) (fmap-c-comp))
      where module pn = PlusN-f n

  constraint-is-functor : ∀ {s : Strata} → Functor (λ n → Constraint n s)
  constraint-is-functor = record { map = fmap-c
                                 ; identity = fmap-c-id
                                 ; composite = fmap-c-comp
                                 }



