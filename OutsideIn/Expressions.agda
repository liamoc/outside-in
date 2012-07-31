open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Expressions(x : X) where  
--  open import OutsideIn.Types
  import OutsideIn.TypeSchema as TS

  open TS(x)
  open X(x)

  {- SYNTAX -}

  -- We index expressions by this structure to inform Agda of the termination order of syntax-directed rules
  -- (de Bruijn indices changing mean that this is not obvious to Agda).
  data Arity : Set where
    Nullary : Arity
    Unary : Arity → Arity
    Binary : Arity → Arity → Arity

  data Name (n : Set) : NameType → Set where
    N : n → Name n Regular
    DC : ∀ {x} → dc x → Name n (Datacon x)

  data Pattern : ℕ → Set where
    Con : ∀ {d} → dc d → Pattern d

  mutual 
    data Alternative (ev tv : Set) : Arity → Set where
      _→′_ : ∀ {n : ℕ}{r : Arity} → Pattern n → Expression (ev ⨁ n) tv r → Alternative ev tv (Unary r)

    data Alternatives (ev tv : Set) : Arity → Set where
      esac : Alternatives ev tv Nullary
      _∣_  : ∀ {r₁ r₂} → Alternative ev tv r₁ → Alternatives ev tv r₂ → Alternatives ev tv (Binary r₁ r₂)

    data Expression (ev tv : Set) : Arity → Set where
      Var : ∀ {x} → Name ev x → Expression ev tv Nullary
      λ′_ : ∀ {a} → Expression (Ⓢ ev) tv a → Expression ev tv (Unary a)
      _·_ : ∀ {a a′} → Expression ev tv a → Expression ev tv a′ → Expression ev tv (Binary a a′)
      let₁_in′_ : ∀ {a a′} → Expression ev tv a → Expression (Ⓢ ev) tv a′ → Expression ev tv (Binary a a′)
      let₂_∷_in′_ : ∀ {a a′} → Expression ev tv a → Type tv → Expression (Ⓢ ev) tv a′ → Expression ev tv (Binary a a′)
      let₃_∷∀_·_⇒_in′_ : ∀ {a a′} → Expression ev tv a → (n : ℕ) 
                                  → QConstraint (tv ⨁ n) 
                                  → Type (tv ⨁ n) 
                                  → Expression (Ⓢ ev) (tv ⨁ n) a′ 
                                  → Expression ev tv (Binary a a′)
      case_of_ : ∀ {r₁ r₂} → Expression ev tv r₁ → Alternatives ev tv r₂ → Expression ev tv (Binary r₁ r₂)

  private
    module PlusN-f n        = Functor (Monad.is-functor (PlusN-is-monad {n}))
    module Ⓢ-f             = Functor Ⓢ-is-functor
    module Type-f           = Functor (type-is-functor)
    module TypeSchema-f {n} = Functor (type-schema-is-functor {n}) 
    module QC-f             = Functor (qconstraint-is-functor) 

  private
    fmap-alt₁ : ∀ {a b tv}{r} → (a → b) → Alternative a tv r → Alternative b tv r
    fmap-exp₁ : ∀ {a b tv}{r} → (a → b) → Expression a tv r → Expression b tv r
    map-fmap-alt₁ : ∀ {a b tv}{r} → (a → b) → Alternatives a tv r → Alternatives b tv r
    fmap-alt₁ f (_→′_ {n} p expr) = p →′ fmap-exp₁ (pn.map f) expr
       where module pn = PlusN-f n
    fmap-exp₁ f (Var (DC c)) = Var (DC c)
    fmap-exp₁ f (Var (N x)) = Var (N (f x))
    fmap-exp₁ f (λ′ x) = λ′ (fmap-exp₁ (Ⓢ-f.map f) x) 
    fmap-exp₁ f (x · y) = (fmap-exp₁ f x) · (fmap-exp₁ f y)
    fmap-exp₁ f (let₁ x in′ y) = let₁ (fmap-exp₁ f x) in′ (fmap-exp₁ (Ⓢ-f.map f) y)
    fmap-exp₁ f (let₂ x ∷ τ in′ y) = let₂ (fmap-exp₁ f x) ∷ τ in′ (fmap-exp₁ (Ⓢ-f.map f) y)
    fmap-exp₁ f (let₃ x ∷∀ n · Q ⇒ τ in′ y) = let₃ fmap-exp₁ f x ∷∀ n · Q ⇒ τ in′ fmap-exp₁ (Ⓢ-f.map f) y
    fmap-exp₁ f (case x of alts) = case (fmap-exp₁ f x) of map-fmap-alt₁ f alts
    map-fmap-alt₁ f esac = esac
    map-fmap-alt₁ f (x ∣ xs) = fmap-alt₁ f x ∣ map-fmap-alt₁ f xs

  private
    fmap-alt₂ : ∀ {a b ev}{r} → (a → b) → Alternative ev a r → Alternative ev b r
    fmap-exp₂ : ∀ {a b ev}{r} → (a → b) → Expression ev a r → Expression ev b r
    map-fmap-alt₂ : ∀ {a b ev}{r} → (a → b) → Alternatives ev a r → Alternatives ev b r
    fmap-alt₂ f (p →′ expr) = p →′ fmap-exp₂ f expr
    fmap-exp₂ f (Var x) = Var x
    fmap-exp₂ f (λ′ x) = λ′ (fmap-exp₂ f x)
    fmap-exp₂ f (x · y) = fmap-exp₂ f x · fmap-exp₂ f y
    fmap-exp₂ f (let₁ x in′ y) = let₁ fmap-exp₂ f x in′ fmap-exp₂ f y
    fmap-exp₂ f (let₂ x ∷ τ in′ y) = let₂ fmap-exp₂ f x ∷ Type-f.map f τ in′ fmap-exp₂ f y
    fmap-exp₂ f (let₃ x ∷∀ n · Q ⇒ τ in′ y) = let₃ fmap-exp₂ f x ∷∀ n · QC-f.map (pn.map f) Q ⇒ Type-f.map (pn.map f) τ 
                                               in′ fmap-exp₂ (pn.map f) y
      where module pn = PlusN-f n
    fmap-exp₂ f (case x of alts) = case (fmap-exp₂ f x) of map-fmap-alt₂ f alts
    map-fmap-alt₂ f esac = esac
    map-fmap-alt₂ f (x ∣ xs) = fmap-alt₂ f x ∣ map-fmap-alt₂ f xs

  private
    fmap-alt-id₁ : {A tv : Set} {f : A → A}{r : Arity} → isIdentity f → isIdentity (fmap-alt₁ {A}{A}{tv}{r} f)   
    map-fmap-alt-id₁ : ∀ {a}{tv}{f : a → a}{r : Arity} → isIdentity f → isIdentity (map-fmap-alt₁  {a}{a}{tv}{r} f)
    fmap-exp-id₁ : ∀{A tv : Set}{r : Arity} {f : A → A} → isIdentity f → isIdentity (fmap-exp₁ {A}{A}{tv}{r} f)   
    fmap-alt-id₁ {A}{f} f-is-id {_→′_ {n} p x} = cong (_→′_ p) (fmap-exp-id₁ (pn.identity f-is-id))
      where module pn = PlusN-f n       
    map-fmap-alt-id₁ {r = Unary _} f-is-id {}
    map-fmap-alt-id₁ {r = Nullary} f-is-id {esac} = refl 
    map-fmap-alt-id₁ {r = Binary r₁ r₂} f-is-id {x ∣ xs} = cong₂ _∣_ (fmap-alt-id₁ f-is-id) (map-fmap-alt-id₁ f-is-id)
    fmap-exp-id₁ {r = Nullary} f-is-id {Var (DC x)} = refl
    fmap-exp-id₁ {r = Nullary} f-is-id {Var (N x)} = cong Var (cong N f-is-id)
    fmap-exp-id₁ {r = Unary r′} f-is-id {λ′ x} = cong λ′_ (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {x · y} = cong₂ _·_ (fmap-exp-id₁ f-is-id) (fmap-exp-id₁ f-is-id)
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {let₁ x in′ y} = cong₂ let₁_in′_ (fmap-exp-id₁ f-is-id) (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {let₂ x ∷ τ in′ y} = cong₂ (λ a b → let₂ a ∷ τ in′ b) (fmap-exp-id₁ f-is-id) 
                                                                                                  (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {let₃ x ∷∀ n · Q ⇒ τ in′ y} = cong₂ (λ a b → let₃ a ∷∀ n · Q ⇒ τ in′ b) 
                                                                                (fmap-exp-id₁ f-is-id) 
                                                                                (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {case x of alts} = cong₂ case_of_ (fmap-exp-id₁ f-is-id) (map-fmap-alt-id₁ f-is-id)

  private
    fmap-alt-id₂ : {A ev : Set}{r : Arity}{f : A → A} → isIdentity f → isIdentity (fmap-alt₂ {A}{A}{ev}{r} f)   
    map-fmap-alt-id₂ : ∀ {a}{ev}{r : Arity}{f : a → a} → isIdentity f → isIdentity (map-fmap-alt₂  {a}{a}{ev}{r} f)
    fmap-exp-id₂ : ∀{A ev : Set}{r : Arity} {f : A → A} → isIdentity f → isIdentity (fmap-exp₂ {A}{A}{ev}{r} f)   
    fmap-alt-id₂ f-is-id {_→′_ {n} p x} = cong (_→′_ p) (fmap-exp-id₂ f-is-id)
      where module pn = PlusN-f n       
    map-fmap-alt-id₂ f-is-id {esac} = refl
    map-fmap-alt-id₂ f-is-id {x ∣ xs} = cong₂ _∣_ (fmap-alt-id₂ f-is-id) (map-fmap-alt-id₂ f-is-id)
    fmap-exp-id₂ {r = Nullary}      f-is-id {Var x} = refl
    fmap-exp-id₂ {r = Unary r′}     f-is-id {λ′ x} = cong λ′_ (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {x · y} = cong₂ _·_ (fmap-exp-id₂ f-is-id) (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {let₁ x in′ y} = cong₂ let₁_in′_ (fmap-exp-id₂ f-is-id) (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {let₂ x ∷ τ in′ y} = cong₃ let₂_∷_in′_ (fmap-exp-id₂ f-is-id) 
                                                                                   (Type-f.identity f-is-id) 
                                                                                   (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {let₃ x ∷∀ n · Q ⇒ τ in′ y} = cong₄ (λ a b c d → let₃ a ∷∀ n · b ⇒ c in′ d) 
                                                                                (fmap-exp-id₂ f-is-id) 
                                                                                (QC-f.identity (pn.identity f-is-id))
                                                                                (Type-f.identity (pn.identity f-is-id)) 
                                                                                (fmap-exp-id₂ (pn.identity f-is-id)) 
      where module pn = PlusN-f n
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {case x of alts} = cong₂ case_of_ (fmap-exp-id₂ f-is-id) (map-fmap-alt-id₂ f-is-id)




  private
    fmap-alt-comp₁ : {r : Arity} {A B C tv : Set} {f : A → B}{g : B → C} {x : Alternative A tv r} 
                  → fmap-alt₁ (g ∘ f) x ≡ fmap-alt₁ g (fmap-alt₁ f x)
    fmap-exp-comp₁ : {r : Arity}{tv A B C : Set} {f : A → B} {g : B → C} {x : Expression A tv r} 
                   → fmap-exp₁ (g ∘ f) x ≡ fmap-exp₁ g (fmap-exp₁ f x)
    map-fmap-alt-comp₁ : ∀{r : Arity}{A B C tv : Set} {f : A → B} {g : B → C} {alts : Alternatives A tv r} 
                      → map-fmap-alt₁ (g ∘ f) alts ≡ map-fmap-alt₁ g (map-fmap-alt₁ f alts)
    fmap-alt-comp₁ {Nullary}{x = ()} 
    fmap-alt-comp₁ {Binary _ _}{x = ()} 
    fmap-alt-comp₁ {Unary r}{f = f}{g}{x = _→′_ {n} p expr} = cong (λ b → _→′_ p b) (trans (cong (λ t → fmap-exp₁ t expr) 
                                                                                                 (extensionality (λ _ → pn.composite))) 
                                                                                           (fmap-exp-comp₁ {f = pn.map f}{g = pn.map g}{expr}))
      where module pn = PlusN-f n  
    map-fmap-alt-comp₁ {alts = esac} = refl
    map-fmap-alt-comp₁ {alts = x ∣ xs} = cong₂ _∣_ fmap-alt-comp₁ map-fmap-alt-comp₁

    fmap-exp-comp₁ {x = Var (N x)} = cong Var (cong N (refl))
    fmap-exp-comp₁ {x = Var (DC x)} = refl
    fmap-exp-comp₁ {f = f}{g}{x = λ′ x } = cong λ′_ (trans (cong (λ t → fmap-exp₁ t x) 
                                                              (extensionality (λ _ → Ⓢ-f.composite))) 
                                                           (fmap-exp-comp₁{f = Ⓢ-f.map f}{Ⓢ-f.map g}{x}))
    fmap-exp-comp₁ {f = f}{g}{x = x · y } = cong₂ _·_ (fmap-exp-comp₁ {f = f}{g}{x}) (fmap-exp-comp₁ {f = f}{g}{y})
    fmap-exp-comp₁ {f = f}{g}{x = let₁ x in′ y } = cong₂ let₁_in′_ (fmap-exp-comp₁ {f = f}{g}{x})
                                                                   (trans (cong (λ t → fmap-exp₁ t y) 
                                                                                (extensionality (λ _ → Ⓢ-f.composite ))) 
                                                                   (fmap-exp-comp₁ {f = Ⓢ-f.map f}{Ⓢ-f.map g}{y}))
    fmap-exp-comp₁ {f = f}{g}{x = let₂ x ∷ τ in′ y} = cong₂ (λ a b → let₂ a ∷ τ in′ b) 
                                                            (fmap-exp-comp₁ {f = f}{g}{x})
                                                            (trans (cong (λ t → fmap-exp₁ t y) 
                                                                         (extensionality (λ _ → Ⓢ-f.composite )))  
                                                                   (fmap-exp-comp₁ {f = Ⓢ-f.map f}{Ⓢ-f.map g}{y}))
    fmap-exp-comp₁ {f = f}{g}{x = let₃ x ∷∀ n · Q ⇒ τ in′ y} = cong₂ (λ a b → let₃ a ∷∀ n · Q ⇒ τ in′ b)
                                                                     (fmap-exp-comp₁ {f = f}{g}{x})
                                                                     (trans (cong (λ t → fmap-exp₁ t y) 
                                                                                  (extensionality (λ _ → Ⓢ-f.composite ))) 
                                                                            (fmap-exp-comp₁ {f = Ⓢ-f.map f}{Ⓢ-f.map g}{y}))
    fmap-exp-comp₁ {f = f}{g}{x = case x of alts } = cong₂ case_of_ (fmap-exp-comp₁ {f = f}{g}{x}) map-fmap-alt-comp₁

  private
    fmap-alt-comp₂ : {A B C ev : Set}{r : Arity} {f : A → B} {g : B → C} {x : Alternative ev A r} 
                   → fmap-alt₂ (g ∘ f) x ≡ fmap-alt₂ g (fmap-alt₂ f x)
    fmap-exp-comp₂ : {A B C ev : Set}{r : Arity} {f : A → B} {g : B → C} {x : Expression ev A r} 
                   → fmap-exp₂ (g ∘ f) x ≡ fmap-exp₂ g (fmap-exp₂ f x)
    map-fmap-alt-comp₂ : ∀{r}{A B C ev : Set} {f : A → B} {g : B → C} {alts : Alternatives ev A r} 
                       → map-fmap-alt₂ (g ∘ f) alts ≡ map-fmap-alt₂ g (map-fmap-alt₂ f alts)
    fmap-alt-comp₂ {x = _→′_ {n} p expr} = cong (_→′_ p) fmap-exp-comp₂
      where module pn = PlusN-f n  
    map-fmap-alt-comp₂ {alts = esac} = refl
    map-fmap-alt-comp₂ {alts = x ∣ xs} = cong₂ _∣_ fmap-alt-comp₂ map-fmap-alt-comp₂

    fmap-exp-comp₂ {x = Var a} = refl
    fmap-exp-comp₂ {x = λ′ x } = cong λ′_ fmap-exp-comp₂
    fmap-exp-comp₂ {x = x · y } = cong₂ _·_ fmap-exp-comp₂ fmap-exp-comp₂
    fmap-exp-comp₂ {x = let₁ x in′ y } = cong₂ let₁_in′_ fmap-exp-comp₂ fmap-exp-comp₂
    fmap-exp-comp₂ {x = let₂ x ∷ τ in′ y } = cong₃ let₂_∷_in′_ fmap-exp-comp₂ Type-f.composite fmap-exp-comp₂
    fmap-exp-comp₂ {x = let₃ x ∷∀ n · Q ⇒ τ in′ y } = cong₄ (λ a b c d → let₃ a ∷∀ n · b ⇒ c in′ d)
                                                            fmap-exp-comp₂ 
                                                            (trans (cong (λ t → QC-f.map t Q) (extensionality (λ _ → pn.composite)))
                                                                   QC-f.composite)
                                                            (trans (cong (λ t → Type-f.map t τ) (extensionality (λ _ → pn.composite))) 
                                                                   Type-f.composite) 
                                                            (trans (cong (λ t → fmap-exp₂ t y) (extensionality (λ _ → pn.composite))) fmap-exp-comp₂)
      where module pn = PlusN-f n
    fmap-exp-comp₂ {x = case x of alts } = cong₂ case_of_ fmap-exp-comp₂ map-fmap-alt-comp₂

  alternatives-is-functor₁ : ∀{tv}{r} → Functor (λ x → Alternatives x tv r)
  alternatives-is-functor₁ = record { map = map-fmap-alt₁; identity = map-fmap-alt-id₁; composite = map-fmap-alt-comp₁ }
  alternatives-is-functor₂ : ∀{ev}{r} → Functor (λ x → Alternatives ev x r)
  alternatives-is-functor₂ = record { map = map-fmap-alt₂; identity = map-fmap-alt-id₂; composite = map-fmap-alt-comp₂ } 
  alternative-is-functor₁ : ∀{tv}{r} → Functor (λ x → Alternative x tv r)
  alternative-is-functor₁ = record { map = fmap-alt₁; identity = fmap-alt-id₁; composite = fmap-alt-comp₁ }
  alternative-is-functor₂ : ∀{ev}{r} → Functor (λ x → Alternative ev x r)
  alternative-is-functor₂ = record { map = fmap-alt₂; identity = fmap-alt-id₂; composite = fmap-alt-comp₂ } 
  expression-is-functor₁ : ∀{tv}{r} → Functor (λ x → Expression x tv r)
  expression-is-functor₁ {tv}{r} = record { map = fmap-exp₁
                                          ; identity = fmap-exp-id₁
                                          ; composite = λ {A}{B}{C}{f}{g}{x} → fmap-exp-comp₁ {r}{tv}{A}{B}{C}{f}{g}{x} 
                                          }
  expression-is-functor₂ : ∀{ev}{r} → Functor (λ x → Expression ev x r)
  expression-is-functor₂ = record { map = fmap-exp₂; identity = fmap-exp-id₂; composite = fmap-exp-comp₂ }


{-
   bind-exp-helper : ∀ {n}{A} → Expression A ⨁ n → Expression (A ⨁ n)
   bind-exp-helper {zero} x = x 
   bind-exp-helper {suc n} v = bind-exp-helper {n} (fmap (cata-Ⓢ (Var zero) (fmap-exp suc)) v)
      where open Functor (Monad.is-functor (PlusN-is-monad {n})) renaming (_<$>_ to fmap)

   bind-exp : ∀ {A B} → Expression A → (A → Expression B) → Expression B
   bind-exp-map : ∀ {n}{A B} → Vec (Alternative A) n → (A → Expression B) → Vec (Alternative B) n
   bind-exp (Var a) f = f a
   bind-exp (λ′ x) f = λ′ (bind-exp x (cata-Ⓢ (Var zero) (fmap-exp suc ∘ f))) 
   bind-exp (bind x) f = λ′ (bind-exp x (cata-Ⓢ (Var zero) (fmap-exp suc ∘ f))) 
   bind-exp (x · y) f =  bind-exp x f · bind-exp y f
   bind-exp (case x of alts) f = case (bind-exp x f) of (bind-exp-map alts f)
   bind-exp-map [] f = []
   bind-exp-map ((_⟶_ {n} p exp) ∷ xs) f = (p ⟶ bind-exp exp (bind-exp-helper {n} ∘ fmap f) ) ∷ bind-exp-map xs f
      where open Functor (Monad.is-functor (PlusN-is-monad {n})) renaming (_<$>_ to fmap)
-}
   {-
   expression-is-monad : Monad Expression
   expression-is-monad = record { is-functor = expression-is-functor
                                ; point = Var
                                ; join = λ p → bind-exp p id 
                                ; is-left-ident = left-id 
                                ; is-right-ident = {!!}
                                ; >=>-assoc = {!!}
                                }
     where open Functor (expression-is-functor)
           module PlusNF{n : ℕ} = Functor (Monad.is-functor (PlusN-is-monad {n})) renaming (_<$>_ to fmap)
           
           left-id : {a : Set} {x : Expression a} → bind-exp (Var <$> x) id ≡ x 
           left-id {x = Var v} = refl
           left-id {x = λ′ x} = cong λ′_ {!!}
           left-id {x = x · y} = cong₂ _·_ left-id left-id
           left-id {x = case x of alts} = cong₂ case_of_ left-id {!!}
 -}