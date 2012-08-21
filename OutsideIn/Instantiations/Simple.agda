open import OutsideIn.Prelude 
open import OutsideIn.X
module OutsideIn.Instantiations.Simple where
  open import Data.Fin hiding (_+_)

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

  data SVar (tc : Set)(n : ℕ) : Set where
    base : tc → SVar tc n
    unification : Fin n → SVar tc n

  thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
  thin zero y          = suc y
  thin (suc x) zero    = zero
  thin (suc x) (suc y) = suc (thin x y)
 
 
  thick : ∀ {n} → (x y : Fin (suc n)) → Ⓢ (Fin n) 
  thick zero zero = zero
  thick zero (suc y) = suc y
  thick {zero } (suc ()) _ 
  thick {suc _} (suc x)  zero = zero
  thick {suc _} (suc x) (suc y) with thick x y
  ... | zero = zero
  ... | suc n = suc (suc n)

  check : ∀ {tc}{n} → Fin (suc n) → Type (SVar tc (suc n)) → Ⓢ (Type (SVar tc n))
  check x (funTy) = suc funTy
  check x (Var (base v)) = suc (Var (base v))
  check x (Var (unification n)) = map (Var ∘ unification) (thick x n) 
   where open Functor (Monad.is-functor Ⓢ-is-monad)
  check x (a · b) = check x a >>= λ a′ →
                     check x b >>= λ b′ → 
                      unit (a′ · b′)
   where open Monad (Ⓢ-is-monad)


  data AList (tc : Set) : ℕ → ℕ → Set where
    anil : ∀ {n} → AList tc n n
    _asnoc_/_ : ∀ {m n} → AList tc m n → Type (SVar tc m) → Fin (suc m) → AList tc (suc m) n


  _∃asnoc_/_ : ∀ {tc}{m} (a : ∃ (AList tc m)) (t' : Type (SVar tc m)) (x : Fin (suc m)) 
             →  ∃ (AList tc (suc m))
  (n , σ) ∃asnoc t' / x = n , σ asnoc t' / x

  _for_ : ∀{tc}{n} → (Type (SVar tc n)) → Fin (suc n)
        → SVar tc (suc n) → Type (SVar tc n)
  (t′ for x) (base y) = Var (base y)
  (t′ for x) (unification y) with thick x y
  ... | suc y′ = Var (unification y′)
  ... | zero   = t′ 

  sub : ∀ {m n}{tc} → AList tc m n → SVar tc m → Type (SVar tc n)  
  sub anil = Var
  sub (σ asnoc t / x) = sub σ >=> (t for x)
    where open Monad (type-is-monad)

  flexFlex : ∀ {tc}{m} (x y : Fin m) → ∃ (AList tc m)    
  flexFlex {_}{suc m} x y with thick x y
  ...              | suc y′ = m , anil asnoc Var (unification y′) / x
  ...              | zero   = suc m , anil
  flexFlex {_}{zero} () _

  flexRigid : ∀ {tc}{m} (x : Fin m) (t : Type (SVar tc m)) -> Ⓢ (∃(AList tc m))
  flexRigid {_}{suc m} x t with check x t
  ...                      | suc t′ = suc (m , anil asnoc t′ / x)
  ...                      | zero   = zero
  flexRigid {_}{zero} () _

  amgu : ∀{tc}{m} → (Eq tc) → (s t : Type (SVar tc m)) → ∃ (AList tc m) → Ⓢ (∃ (AList tc m))
  amgu eq (funTy) (funTy) acc = suc acc 
  amgu eq (Var (base a)) (Var (base b)) acc with eq a b
  ... | true = suc acc 
  ... | false = zero 
  amgu eq (Var (base a)) (funTy) acc = zero 
  amgu eq (funTy) (Var (base b)) acc = zero 
  amgu eq (funTy) (a · b) acc = zero
  amgu eq (Var (base _)) (a · b) acc = zero
  amgu eq (a · b) (funTy) acc = zero
  amgu eq (a · b) (Var (base _)) acc = zero
  amgu eq (a · b) (a′ · b′) acc = amgu eq a a′ acc >>= amgu eq b b′ 
     where open Monad (Ⓢ-is-monad)
  amgu eq (Var (unification x)) (Var (unification y)) (m , anil) = suc (flexFlex x y)
  amgu eq (Var (unification x)) t (m , anil) = flexRigid x t 
  amgu eq t (Var (unification x)) (m , anil) = flexRigid x t 
  amgu eq s t (n , σ asnoc r / z) = Ⓢ-f.map (λ σ → σ ∃asnoc r / z) (amgu eq (s >>= (r for z)) 
                                                                             (t >>= (r for z)) 
                                                                             (n , σ)) 
    where module Ⓢ-f = Functor (Monad.is-functor Ⓢ-is-monad)
          open Monad (type-is-monad)


  mgu : ∀{tc}{m}(eq : Eq tc)(s t : Type (SVar tc m)) → Ⓢ (∃ (AList tc m))
  mgu {m = m} eq s t = amgu eq s t (m , anil)


  prf : ∀ {m n} → m + suc n ≡ suc m + n
  prf {zero} = refl
  prf {suc n} = cong suc (prf {n})
  prf₂ : ∀ {m} →  m + zero ≡ m
  prf₂ {zero} = refl
  prf₂ {suc n} = cong suc prf₂

  svar-iso₁′ : ∀{m n}{tc} → SVar tc n ⨁ m → SVar tc (m + n) 
  svar-iso₁′ {zero} x = x
  svar-iso₁′ {suc m}{n}{tc} v = subst (SVar tc) (prf {m}{n}) (svar-iso₁′ {m}{suc n} (pm-f.map ind v)) 
   where module pm-f = Functor (Monad.is-functor (PlusN-is-monad {m}))
         ind : ∀{tc}{m} → Ⓢ (SVar tc m) → SVar tc (suc m)
         ind zero = unification zero
         ind (suc n) with n
         ... | base v = base v
         ... | unification x = unification (suc x)


  svar-iso₂′ : ∀{m}{tc} → Fin m → tc ⨁ m 
  svar-iso₂′ {zero} () 
  svar-iso₂′ {suc n} zero = pn-m.unit zero 
   where module pn-m = Monad (PlusN-is-monad {n})
  svar-iso₂′ {suc n} (suc v) = pm-f.map suc (svar-iso₂′ {n} v)
   where module pm-f = Functor (Monad.is-functor (PlusN-is-monad {n}))

  svar-iso₁ : ∀{m}{tc} → tc ⨁ m → SVar tc m
  svar-iso₁ {m}{tc} v = subst (SVar tc) prf₂ (svar-iso₁′ {m}{zero}{tc} (pm-f.map base v))
   where module pm-f = Functor (Monad.is-functor (PlusN-is-monad {m}))

  svar-iso₂ : ∀{m}{tc} → SVar tc m → tc ⨁ m 
  svar-iso₂ {m}{tc} (base v) = pm-m.unit v
   where module pm-m = Monad (PlusN-is-monad {m})
  svar-iso₂ {m}{tc} (unification v) = svar-iso₂′ v
  
  open Functor (Monad.is-functor type-is-monad) using () renaming (map to τ-map)

  mgu′ : ∀{tc}{m}(eq : Eq tc)(s t : Type (tc ⨁ m)) → Ⓢ (∃ (λ n → tc ⨁ m → Type (tc ⨁ n)))
  mgu′ {tc}{m} eq s t with mgu {tc}{m} eq (τ-map svar-iso₁ s) (τ-map svar-iso₁ t)
  ... | zero = zero
  ... | suc (n , al) = suc (n , τ-map svar-iso₂ ∘ sub al ∘ svar-iso₁)


  data SConstraintShape (x : Set) : Shape → Set where
     _∼_ : Type x → Type x → SConstraintShape x Nullary
     ε : SConstraintShape x Nullary
     _∧′_ : ∀ {a b} → SConstraintShape x a → SConstraintShape x b → SConstraintShape x (Binary a b)
 

  applySubst : ∀ {a b}{s} → (a → Type b) → SConstraintShape a s → SConstraintShape b s
  applySubst f (a ∼ b) = (a >>= f) ∼ (b >>= f)
    where open Monad (type-is-monad)
  applySubst f (a ∧′ b) = applySubst f a ∧′ applySubst f b
  applySubst f (ε) = ε




  constraint-types : ∀{a b} → (Type a → Type b) → (SConstraint a → SConstraint b)  
  constraint-types f ε = ε 
  constraint-types f (a ∧′ b) = constraint-types f a ∧′ constraint-types f b
  constraint-types f (a ∼ b) = f a ∼ f b 

  applySubst′ : ∀ {a b} → (a → Type b) → SConstraint a  → SConstraint b 
  applySubst′ f (a ∼ b) = (a >>= f) ∼ (b >>= f)
    where open Monad (type-is-monad)
  applySubst′ f (a ∧′ b) = applySubst′ f a ∧′ applySubst′ f b
  applySubst′ f (ε) = ε
  


  constraint : ∀{s}{tc}{m} → Eq tc → SConstraintShape (tc ⨁ m) s 
             → SimplifierResult tc m
  constraint {Unary _} _ ()
  constraint {Nullary}{tc}{m} eq ε = Solved {m = m} Var
  constraint {Nullary}{tc}{m} eq (a ∼ b) with mgu′ {tc}{m} eq a b
  ... | suc (n , θ) = Solved {m = n} θ
  ... | zero = Unsolved {m = m} (a ∼ b) Var
  constraint {Binary r₁ r₂}{tc}{m} eq (a ∧′ b) with constraint {r₁}{tc}{m} eq a
  ... | Unsolved {n} Qr θ with constraint {r₂}{tc}{n} eq (applySubst θ b)
  ...                     | Solved {n′} θ′ = Unsolved {m = n′} (applySubst′ θ′ Qr) (θ′ >=> θ)
    where open Monad (type-is-monad)
  ...                     | Unsolved {n′} Qr′ θ′ = Unsolved {m = n′} (Qr′ ∧′ applySubst′ θ′ Qr) (θ′ >=> θ)
    where open Monad (type-is-monad)
  constraint {Binary r₁ r₂}{tc}{m} eq (a ∧′ b) | Solved {n} θ 
                with constraint {r₂}{tc}{n} eq (applySubst θ b) 
  ...           | Unsolved {n′} Qr′ θ′  = Unsolved {m = n′} Qr′ (θ′ >=> θ)  
    where open Monad (type-is-monad)
  ...           | Solved {n′} θ′ = Solved {m = n′} (θ′ >=> θ)
    where open Monad (type-is-monad)

  shapify : ∀ {a} → SConstraint a → ∃ (SConstraintShape a)
  shapify (a ∼ b) = Nullary , a ∼ b
  shapify (a ∧′ b) with shapify a | shapify b
  ... | r₁ , a′ | r₂ , b′ = Binary r₁ r₂ , a′ ∧′ b′
  shapify (ε) = Nullary , ε
  

  simplifier : {x : Set} → Eq x → (n : ℕ) → Ax → SConstraint (x ⨁ n) 
                         → SConstraint (x ⨁ n) → SimplifierResult x n
  simplifier {x} eq n _ con₁ con₂ with shapify (con₁ ∧′ con₂) 
  ... | r , v = constraint {r}{x}{n} eq v
     
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


