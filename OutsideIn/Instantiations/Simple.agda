open import OutsideIn.Prelude 
open import OutsideIn.X
module OutsideIn.Instantiations.Simple where

  data Type ( n :  Set) : Set where
    funTy : Type n
    _·_   : Type n → Type n → Type n
    Var   : n → Type n

  private
    fmap-τ : ∀ {a b} → (a → b) → Type a → Type b
    fmap-τ f (funTy) = funTy
    fmap-τ f (x · y) = fmap-τ f x · fmap-τ f y
    fmap-τ f (Var v) = Var (f v)
    fmap-τ-id : ∀   {A : Set} {f : A → A} → isIdentity f → isIdentity (fmap-τ f)
    fmap-τ-id {f = f} isid {funTy} = refl
    fmap-τ-id {f = f} isid {α ·  β} = cong₂ _·_  (fmap-τ-id isid) (fmap-τ-id isid)
    fmap-τ-id {f = f} isid {Var  v} = cong Var isid
    fmap-τ-comp : {A B C : Set} {f : A → B} {g : B → C} {x : Type A}       
                → fmap-τ (g ∘ f) x ≡ fmap-τ g (fmap-τ f x)
    fmap-τ-comp {x = funTy} = refl
    fmap-τ-comp {x = α ·  β} = cong₂ _·_ fmap-τ-comp fmap-τ-comp
    fmap-τ-comp {x = Var v}  = cong Var refl 

  type-is-functor : Functor Type  
  type-is-functor = record { map = fmap-τ
                           ; identity = fmap-τ-id
                           ; composite = fmap-τ-comp
                           }
  type-is-monad : Monad Type 
  type-is-monad = record { is-functor = type-is-functor
                         ; point = Var
                         ; join = join-τ
                         ; is-left-ident  = left-id 
                         ; is-right-ident = refl 
                         ; >=>-assoc = λ {_}{_}{_}{_}{_}{_}{c}{v} → assoc {τ = c v}
                         }
     where join-τ :{a : Set} → Type (Type a)  → Type a
           join-τ (funTy) = funTy
           join-τ (x · y) = join-τ x · join-τ y
           join-τ (Var v) = v
 
           open Functor (type-is-functor)
           assoc : ∀{A B C}{a : B → Type C}{b : A → Type B}{τ : Type A} 
                 → join-τ (fmap-τ a (join-τ (fmap-τ b τ))) 
                 ≡ join-τ (fmap-τ (λ v' → join-τ (fmap-τ a (b v'))) τ)
           assoc {a = a}{b}{funTy} = refl
           assoc {a = a}{b}{α  · β} = cong₂ _·_  (assoc {τ = α}) (assoc {τ = β})
           assoc {a = a}{b}{Var  v} = refl 
           left-id : ∀ {a}{τ : Type a} → join-τ (Var <$> τ) ≡ τ
           left-id {_}{funTy} = refl
           left-id {_}{α ·  β} = cong₂ _·_  (left-id {τ = α}) (left-id {τ = β})
           left-id {_}{Var  v} = refl

  data SConstraint (x : Set) : Set where
     _∼_ : Type x → Type x → SConstraint x
     _∧′_ : SConstraint x → SConstraint x → SConstraint x
     ε : SConstraint x 

  sconstraint-is-functor : Functor SConstraint 
  sconstraint-is-functor = record { map = s-map; identity = s-ident; composite = s-comp }
     where open Functor (type-is-functor)
           s-map : {A B : Set} → (A → B) → SConstraint A → SConstraint B
           s-map f (ε) = ε
           s-map f (a ∼ b) = map f a ∼ map f b
           s-map f (a ∧′ b) = s-map f a ∧′ s-map f b
           s-ident : {A : Set} {f : A → A} → isIdentity f → isIdentity (s-map f)
           s-ident isid {ε} = refl
           s-ident isid {a ∼ b} = cong₂ _∼_ (identity isid) (identity isid) 
           s-ident isid {a ∧′ b} = cong₂ _∧′_ (s-ident isid) (s-ident isid) 
           s-comp : {A B C : Set} {f : A → B} {g : B → C} {x : SConstraint A} 
                  → s-map (g ∘ f) x ≡ s-map g (s-map f x)
           s-comp {x = ε} = refl
           s-comp {x = a ∼ b} = cong₂ _∼_ composite composite
           s-comp {x = a ∧′ b} = cong₂ _∧′_ s-comp s-comp

  data Ax : Set where ax : Ax

  _⟶_ : ∀ {n} → Type n → Type n → Type n
  a ⟶ b = (funTy · a) · b

  open SimpRes(SConstraint)(Type)

  postulate simplifier : {x : Set} (n : ℕ) → Ax → SConstraint (x ⨁ n) → SConstraint (x ⨁ n) 
                       → SimplifierResult x n

  Simple : (ℕ → Set) → X
  Simple dc = record { dc = dc
                     ; Type = Type
                     ; QConstraint = SConstraint
                     ; type-is-monad = type-is-monad
                     ; qconstraint-is-functor = sconstraint-is-functor
                     ; funType = _⟶_; appType = _·_
                     ; _∼_ = _∼_; _∧_ = _∧′_; ε = ε 
                     ; AxiomScheme = Ax
                     ; simplifier = simplifier
                     ; constraint-types = constraint-types 
                     }
     where constraint-types : ∀{a b} → (Type a → Type b) → (SConstraint a → SConstraint b)  
           constraint-types f ε = ε 
           constraint-types f (a ∧′ b) = constraint-types f a ∧′ constraint-types f b
           constraint-types f (a ∼ b) = f a ∼ f b 

