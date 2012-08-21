open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Expressions(x : X) where  
  import OutsideIn.TypeSchema as TS
  open TS(x)
  open X(x)

  {- SYNTAX -}
  data Name (n : Set) : NameType → Set where
    N : n → Name n Regular
    DC : ∀ {x} → dc x → Name n (Datacon x)

  data Pattern : ℕ → Set where
    Con : ∀ {d} → dc d → Pattern d

  mutual 
    data Alternative (ev tv : Set) : Shape → Set where
      _→′_ : ∀ {n : ℕ}{r : Shape} → Pattern n → Expression (ev ⨁ n) tv r 
           → Alternative ev tv (Unary r)

    infixr 5 _∣_ 

    data Alternatives (ev tv : Set) : Shape → Set where
      esac : Alternatives ev tv Nullary
      _∣_  : ∀ {r₁ r₂} → Alternative ev tv r₁ → Alternatives ev tv r₂ 
           → Alternatives ev tv (Binary r₁ r₂)

    data Expression (ev tv : Set) : Shape → Set where
      Var : ∀ {x} → Name ev x → Expression ev tv Nullary
      λ′_ : ∀ {a} → Expression (Ⓢ ev) tv a → Expression ev tv (Unary a)
      _·_ : ∀ {a a′} → Expression ev tv a → Expression ev tv a′ → Expression ev tv (Binary a a′)
      let₁_in′_ : ∀ {a a′} → Expression ev tv a → Expression (Ⓢ ev) tv a′ 
                → Expression ev tv (Binary a a′)
      let₂_∷_in′_ : ∀ {a a′} → Expression ev tv a → Type tv → Expression (Ⓢ ev) tv a′ 
                  → Expression ev tv (Binary a a′)
      let₃_·_∷_⇒_in′_ : ∀ {a a′} → (n : ℕ) → Expression ev (tv ⨁ n) a  
                                  → QConstraint (tv ⨁ n) 
                                  → Type (tv ⨁ n) 
                                  → Expression (Ⓢ ev) tv a′ 
                                  → Expression ev tv (Binary a a′)
      case_of_ : ∀ {r₁ r₂} → Expression ev tv r₁ → Alternatives ev tv r₂ 
               → Expression ev tv (Binary r₁ r₂)

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
    fmap-exp₁ f (let₃ n · x ∷ Q ⇒ τ in′ y) = let₃  n · fmap-exp₁ f x ∷ Q ⇒ τ 
                                              in′ fmap-exp₁ (Ⓢ-f.map f) y
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
    fmap-exp₂ f (let₃ n · x ∷ Q ⇒ τ in′ y) = let₃ n · fmap-exp₂ (pn.map f) x 
                                                ∷ QC-f.map (pn.map f) Q ⇒ Type-f.map (pn.map f) τ 
                                               in′ fmap-exp₂ f y
      where module pn = PlusN-f n
    fmap-exp₂ f (case x of alts) = case (fmap-exp₂ f x) of map-fmap-alt₂ f alts
    map-fmap-alt₂ f esac = esac
    map-fmap-alt₂ f (x ∣ xs) = fmap-alt₂ f x ∣ map-fmap-alt₂ f xs

  private
    fmap-alt-id₁ : {A tv : Set} {f : A → A}{r : Shape} 
                 → isIdentity f → isIdentity (fmap-alt₁ {A}{A}{tv}{r} f)   
    map-fmap-alt-id₁ : ∀ {a}{tv}{f : a → a}{r : Shape} 
                     → isIdentity f → isIdentity (map-fmap-alt₁  {a}{a}{tv}{r} f)
    fmap-exp-id₁ : ∀{A tv : Set}{r : Shape} {f : A → A} → isIdentity f 
                 → isIdentity (fmap-exp₁ {A}{A}{tv}{r} f)   
    fmap-alt-id₁ {A}{f} f-is-id {_→′_ {n} p x} = cong (_→′_ p) (fmap-exp-id₁ (pn.identity f-is-id))
      where module pn = PlusN-f n       
    map-fmap-alt-id₁ {r = Unary _} f-is-id {}
    map-fmap-alt-id₁ {r = Nullary} f-is-id {esac} = refl 
    map-fmap-alt-id₁ {r = Binary r₁ r₂} f-is-id {x ∣ xs} = cong₂ _∣_ (fmap-alt-id₁ f-is-id) 
                                                                     (map-fmap-alt-id₁ f-is-id)
    fmap-exp-id₁ {r = Nullary} f-is-id {Var (DC x)} = refl
    fmap-exp-id₁ {r = Nullary} f-is-id {Var (N x)} = cong Var (cong N f-is-id)
    fmap-exp-id₁ {r = Unary r′} f-is-id {λ′ x} = cong λ′_ (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {x · y} = cong₂ _·_ (fmap-exp-id₁ f-is-id) 
                                                                (fmap-exp-id₁ f-is-id)
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {let₁ x in′ y} 
      = cong₂ let₁_in′_ (fmap-exp-id₁ f-is-id) (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {let₂ x ∷ τ in′ y} 
      = cong₂ (λ a b → let₂ a ∷ τ in′ b) (fmap-exp-id₁ f-is-id) 
                                         (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {let₃ n · x ∷ Q ⇒ τ in′ y} 
      = cong₂ (λ a b → let₃ n · a ∷ Q ⇒ τ in′ b) (fmap-exp-id₁ f-is-id) 
                                                 (fmap-exp-id₁ (Ⓢ-f.identity f-is-id))
    fmap-exp-id₁ {r = Binary r₁ r₂} f-is-id {case x of alts} 
      = cong₂ case_of_ (fmap-exp-id₁ f-is-id) (map-fmap-alt-id₁ f-is-id)

  private
    fmap-alt-id₂ : {A ev : Set}{r : Shape}{f : A → A} 
                 → isIdentity f → isIdentity (fmap-alt₂ {A}{A}{ev}{r} f)   
    map-fmap-alt-id₂ : ∀ {a}{ev}{r : Shape}{f : a → a} 
                     → isIdentity f → isIdentity (map-fmap-alt₂  {a}{a}{ev}{r} f)
    fmap-exp-id₂ : ∀{A ev : Set}{r : Shape} {f : A → A}
                 → isIdentity f → isIdentity (fmap-exp₂ {A}{A}{ev}{r} f)   
    fmap-alt-id₂ f-is-id {_→′_ {n} p x} = cong (_→′_ p) (fmap-exp-id₂ f-is-id)
    map-fmap-alt-id₂ f-is-id {esac} = refl
    map-fmap-alt-id₂ f-is-id {x ∣ xs} = cong₂ _∣_ (fmap-alt-id₂ f-is-id) (map-fmap-alt-id₂ f-is-id)
    fmap-exp-id₂ {r = Nullary}      f-is-id {Var x} = refl
    fmap-exp-id₂ {r = Unary r′}     f-is-id {λ′ x} = cong λ′_ (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {x · y} = cong₂ _·_ (fmap-exp-id₂ f-is-id) 
                                                                (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {let₁ x in′ y} = cong₂ let₁_in′_ (fmap-exp-id₂ f-is-id)
                                                                             (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {let₂ x ∷ τ in′ y} = cong₃ let₂_∷_in′_ 
                                                                       (fmap-exp-id₂ f-is-id) 
                                                                       (Type-f.identity f-is-id) 
                                                                       (fmap-exp-id₂ f-is-id)
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {let₃ n · x ∷ Q ⇒ τ in′ y} 
      = cong₄ (let₃_·_∷_⇒_in′_ n) (fmap-exp-id₂ (pn.identity f-is-id)) 
                                  (QC-f.identity (pn.identity f-is-id))
                                  (Type-f.identity (pn.identity f-is-id)) 
                                  (fmap-exp-id₂ f-is-id)
      where module pn = PlusN-f n
    fmap-exp-id₂ {r = Binary r₁ r₂} f-is-id {case x of alts} 
      = cong₂ case_of_ (fmap-exp-id₂ f-is-id) (map-fmap-alt-id₂ f-is-id)




  private
    fmap-alt-comp₁ : {r : Shape} {A B C tv : Set} {f : A → B}{g : B → C} {x : Alternative A tv r} 
                   → fmap-alt₁ (g ∘ f) x ≡ fmap-alt₁ g (fmap-alt₁ f x)
    fmap-exp-comp₁ : {r : Shape}{tv A B C : Set} {f : A → B} {g : B → C} {x : Expression A tv r} 
                   → fmap-exp₁ (g ∘ f) x ≡ fmap-exp₁ g (fmap-exp₁ f x)
    map-fmap-alt-comp₁ : {r : Shape}{A B C tv : Set}{f : A → B}{g : B → C}{l : Alternatives A tv r} 
                       → map-fmap-alt₁ (g ∘ f) l ≡ map-fmap-alt₁ g (map-fmap-alt₁ f l)
    fmap-alt-comp₁ {Nullary}   {x = ()} 
    fmap-alt-comp₁ {Binary _ _}{x = ()} 
    fmap-alt-comp₁ {Unary r}{f = f}{g}{x = _→′_ {n} p expr} 
      = cong (_→′_ p) 
             (combine-composite′ ⦃ Monad.is-functor (PlusN-is-monad {n}) ⦄ {expr} 
                                 fmap-exp₁ 
                                 (fmap-exp-comp₁ {f = pn.map f}{g = pn.map g}{expr}))
      where module pn = PlusN-f n
    map-fmap-alt-comp₁ {l = esac} = refl
    map-fmap-alt-comp₁ {l = x ∣ xs} = cong₂ _∣_ fmap-alt-comp₁ map-fmap-alt-comp₁

    fmap-exp-comp₁ {x = Var (N x)} = cong Var (cong N (refl))
    fmap-exp-comp₁ {x = Var (DC x)} = refl
    fmap-exp-comp₁ {f = f}{g}{x = λ′ x } 
      = cong λ′_ (combine-composite′ ⦃ Monad.is-functor (Ⓢ-is-monad) ⦄ {x}
                                     fmap-exp₁
                                     (fmap-exp-comp₁ {f = Ⓢ-f.map f}{g = Ⓢ-f.map g}{x}))
    fmap-exp-comp₁ {f = f}{g}{x = x · y } = cong₂ _·_ (fmap-exp-comp₁ {f = f}{g}{x}) 
                                                      (fmap-exp-comp₁ {f = f}{g}{y})
    fmap-exp-comp₁ {f = f}{g}{x = let₁ x in′ y } 
      = cong₂ let₁_in′_ (fmap-exp-comp₁ {f = f}{g}{x})
                        (combine-composite′ ⦃ Monad.is-functor (Ⓢ-is-monad) ⦄ {y}
                                     fmap-exp₁
                                     (fmap-exp-comp₁ {f = Ⓢ-f.map f}{g = Ⓢ-f.map g}{y}))
    fmap-exp-comp₁ {f = f}{g}{x = let₂ x ∷ τ in′ y} 
      = cong₂ (λ a b → let₂ a ∷ τ in′ b) (fmap-exp-comp₁ {f = f}{g}{x})
                                         (combine-composite′ ⦃ Monad.is-functor (Ⓢ-is-monad) ⦄ {y}
                                                             fmap-exp₁
                                                             (fmap-exp-comp₁ {f = Ⓢ-f.map f}
                                                                             {g = Ⓢ-f.map g}{y}))
    fmap-exp-comp₁ {f = f}{g}{x = let₃ n · x ∷ Q ⇒ τ in′ y} 
      = cong₂ (λ a b → let₃ n · a ∷ Q ⇒ τ in′ b) 
              (fmap-exp-comp₁ {f = f}{g}{x})
              (combine-composite′ ⦃ Monad.is-functor (Ⓢ-is-monad) ⦄ {y}
                                  fmap-exp₁
                                  (fmap-exp-comp₁ {f = Ⓢ-f.map f}{g = Ⓢ-f.map g}{y}))
    fmap-exp-comp₁ {f = f}{g}{x = case x of alts } = cong₂ case_of_ 
                                                           (fmap-exp-comp₁ {f = f}{g}{x}) 
                                                           map-fmap-alt-comp₁

  private
    fmap-alt-comp₂ : {A B C ev : Set}{r : Shape} {f : A → B} {g : B → C} {x : Alternative ev A r} 
                   → fmap-alt₂ (g ∘ f) x ≡ fmap-alt₂ g (fmap-alt₂ f x)
    fmap-exp-comp₂ : {A B C ev : Set}{r : Shape} {f : A → B} {g : B → C} {x : Expression ev A r} 
                   → fmap-exp₂ (g ∘ f) x ≡ fmap-exp₂ g (fmap-exp₂ f x)
    map-fmap-alt-comp₂ : ∀{r}{A B C ev : Set} {f : A → B} {g : B → C} {alts : Alternatives ev A r} 
                       → map-fmap-alt₂ (g ∘ f) alts ≡ map-fmap-alt₂ g (map-fmap-alt₂ f alts)
    fmap-alt-comp₂ {x = _→′_ {n} p expr} = cong (_→′_ p) fmap-exp-comp₂
    map-fmap-alt-comp₂ {alts = esac} = refl
    map-fmap-alt-comp₂ {alts = x ∣ xs} = cong₂ _∣_ fmap-alt-comp₂ map-fmap-alt-comp₂

    fmap-exp-comp₂ {x = Var a} = refl
    fmap-exp-comp₂ {x = λ′ x } = cong λ′_ fmap-exp-comp₂
    fmap-exp-comp₂ {x = x · y } = cong₂ _·_ fmap-exp-comp₂ fmap-exp-comp₂
    fmap-exp-comp₂ {x = let₁ x in′ y } = cong₂ let₁_in′_ fmap-exp-comp₂ fmap-exp-comp₂
    fmap-exp-comp₂ {x = let₂ x ∷ τ in′ y } = cong₃ let₂_∷_in′_ fmap-exp-comp₂ Type-f.composite fmap-exp-comp₂
    fmap-exp-comp₂ {x = let₃ n · x ∷ Q ⇒ τ in′ y } 
      = cong₄ (λ a b c d → let₃ n · a ∷ b ⇒ c in′ d)
              (combine-composite′ ⦃ pnf ⦄ fmap-exp₂ fmap-exp-comp₂)
              (combine-composite ⦃ qconstraint-is-functor ⦄ ⦃ pnf ⦄)
              (combine-composite ⦃ type-is-functor        ⦄ ⦃ pnf ⦄)
              fmap-exp-comp₂
      where pnf = Monad.is-functor (PlusN-is-monad {n})
    fmap-exp-comp₂ {x = case x of alts } = cong₂ case_of_ fmap-exp-comp₂ map-fmap-alt-comp₂

  alternatives-is-functor₁ : ∀{tv}{r} → Functor (λ x → Alternatives x tv r)
  alternatives-is-functor₁ = record { map = map-fmap-alt₁
                                    ; identity = map-fmap-alt-id₁
                                    ; composite = map-fmap-alt-comp₁ 
                                    }
  alternatives-is-functor₂ : ∀{ev}{r} → Functor (λ x → Alternatives ev x r)
  alternatives-is-functor₂ = record { map = map-fmap-alt₂
                                    ; identity = map-fmap-alt-id₂
                                    ; composite = map-fmap-alt-comp₂ 
                                    } 
  alternative-is-functor₁ : ∀{tv}{r} → Functor (λ x → Alternative x tv r)
  alternative-is-functor₁ = record { map = fmap-alt₁
                                   ; identity = fmap-alt-id₁
                                   ; composite = fmap-alt-comp₁ 
                                   }
  alternative-is-functor₂ : ∀{ev}{r} → Functor (λ x → Alternative ev x r)
  alternative-is-functor₂ = record { map = fmap-alt₂
                                   ; identity = fmap-alt-id₂
                                   ; composite = fmap-alt-comp₂ 
                                   } 
  expression-is-functor₁ : ∀{tv}{r} → Functor (λ x → Expression x tv r)
  expression-is-functor₁ {tv}{r} = record { map = fmap-exp₁
                                          ; identity = fmap-exp-id₁
                                          ; composite = λ {A}{B}{C}{f}{g}{x} 
                                                        → fmap-exp-comp₁ {r}{tv}{A}{B}{C}{f}{g}{x} 
                                          }
  expression-is-functor₂ : ∀{ev}{r} → Functor (λ x → Expression ev x r)
  expression-is-functor₂ = record { map = fmap-exp₂
                                  ; identity = fmap-exp-id₂
                                  ; composite = fmap-exp-comp₂ 
                                  }

