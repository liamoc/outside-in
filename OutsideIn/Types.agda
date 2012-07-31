open import OutsideIn.Prelude 
module OutsideIn.Types where

  data Type ( n :  Set) : Set where
    _⟶_ : Type n → Type n → Type n
    _·_  : Type n → Type n → Type n
    Var  : n → Type n

  private
    fmap-τ : ∀ {a b} → (a → b) → Type a → Type b
    fmap-τ f (α ⟶ β) = fmap-τ f α ⟶ fmap-τ f β
    fmap-τ f (x · y) = fmap-τ f x · fmap-τ f y
    fmap-τ f (Var v) = Var (f v)
    fmap-τ-id : ∀   {A : Set} {f : A → A} → isIdentity f → isIdentity (fmap-τ f)
    fmap-τ-id {f = f} isid {α ⟶ β} = cong₂ _⟶_ (fmap-τ-id isid) (fmap-τ-id isid)
    fmap-τ-id {f = f} isid {α ·  β} = cong₂ _·_  (fmap-τ-id isid) (fmap-τ-id isid)
    fmap-τ-id {f = f} isid {Var  v} = cong Var isid
    fmap-τ-comp : {A B C : Set} {f : A → B} {g : B → C} {x : Type A}       
                → fmap-τ (g ∘ f) x ≡ fmap-τ g (fmap-τ f x)
    fmap-τ-comp {x = α ⟶ β} = cong₂ _⟶_ fmap-τ-comp fmap-τ-comp
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
           join-τ (α ⟶ β) = join-τ α ⟶ join-τ β
           join-τ (x · y) = join-τ x · join-τ y
           join-τ (Var v) = v
 
           open Functor (type-is-functor)
           assoc : ∀{A B C}{a : B → Type C}{b : A → Type B}{τ : Type A} 
                 → join-τ (fmap-τ a (join-τ (fmap-τ b τ))) ≡ join-τ (fmap-τ (λ v' → join-τ (fmap-τ a (b v'))) τ)
           assoc {a = a}{b}{α ⟶ β} = cong₂ _⟶_ (assoc {τ = α}) (assoc {τ = β})
           assoc {a = a}{b}{α  · β} = cong₂ _·_  (assoc {τ = α}) (assoc {τ = β})
           assoc {a = a}{b}{Var  v} = refl 
           left-id : ∀ {a}{τ : Type a} → join-τ (Var <$> τ) ≡ τ
           left-id {_}{α ⟶ β} = cong₂ _⟶_ (left-id {τ = α}) (left-id {τ = β})
           left-id {_}{α ·  β} = cong₂ _·_  (left-id {τ = α}) (left-id {τ = β})
           left-id {_}{Var  v} = refl

