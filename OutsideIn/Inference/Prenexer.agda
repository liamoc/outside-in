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


  data _⟶!_ {n : Set} : Constraint n Extended → Constraint n Extended → Set where
    PN-QC : ∀ {x} → QC x ⟶! QC x
    PN-∧  : ∀ {a b}{na nb}{a′}{b′} → a ⟶! (Ⅎ′ na · a′) → b ⟶! (Ⅎ′ nb · b′) → (a ∧′ b) ⟶! (Ⅎ′ na · (Ⅎ′ nb · (Constraint-f.map (PlusN-m.unit nb) a′ ∧′ Constraint-f.map (PlusN-f.map nb (PlusN-m.unit na)) b′)))
    PN-Imp : ∀ {q}{c}{m}{c′} → c ⟶! (Ⅎ′ m · c′) → (Imp′ q c) ⟶! (Imp′ q (Ⅎ′ m · c′))
    PN-Frs : ∀ {c}{c′} → c ⟶! c′ → (Ⅎ c) ⟶! (Ⅎ c′)

  data _flatten:_  {n : Set} : Constraint n Extended → Constraint n Flat → Set where
    FL-QC : ∀{x} → (QC x) flatten: (QC x)
    FL-∧  : ∀ {a b}{a′ b′} → a flatten: a′ → b flatten: b′ → (a ∧′ b) flatten: (a′ ∧′ b′)
    FL-Imp : ∀{m}{q}{c}{c′} → Imp′ q (Ⅎ′ m · c) flatten: Imp (∃ m · q ⊃ c′)

  
  collectℲ : ∀ {x}{n m}{C : Constraint _ Extended} 
           →  (Ⅎ′ n · Ⅎ′ m · C) ≡ (Ⅎ′ (n + m) · subst (λ x → Constraint x Extended) (sym (PlusN-collect {x}{n}{m})) C)
  collectℲ {x}{0}{m} = refl                                               
  collectℲ {x}{suc n}{m} = cong Ⅎ_ (collectℲ {Ⓢ x}{n}{m})                                               

  fmap-into-Ⅎs : ∀{A B}{f : A → B}{n}{C : Constraint (A ⨁ n) Extended} → Constraint-f.map f (Ⅎ′ n · C) ≡ Ⅎ′ n · Constraint-f.map (PlusN-f.map n f) C 
  fmap-into-Ⅎs {n = 0} = refl
  fmap-into-Ⅎs {n = suc n} = cong Ⅎ_ (fmap-into-Ⅎs {n = n})

  flatten-fmap : ∀ {A}{B}{a : Constraint A Extended}{a′ : Constraint A Flat}{f : A → B} 
               → a flatten: a′ → Constraint-f.map f a flatten: Constraint-f.map f a′
  flatten-fmap (FL-QC) = FL-QC 
  flatten-fmap (FL-∧ p₁ p₂) = FL-∧ (flatten-fmap p₁) (flatten-fmap p₂) 
  flatten-fmap {f = f}(FL-Imp {m}{q}{c}{c′}) = subst (λ c → Imp′ (QC-f.map f q) c flatten: Constraint-f.map f (Imp (∃ m · q ⊃ c′))) 
                                                     (sym (fmap-into-Ⅎs {f = f}{m})) FL-Imp

  subst-is-fmap : ∀{A}{B}{P : A ≡ B}{s}{C : Constraint A s} → subst (λ x₁ → Constraint x₁ s) P C ≡ Constraint-f.map (subst id P) C
  subst-is-fmap {A}{.A}{refl} = (sym (Constraint-f.identity help))
    where help : ∀{A} → isIdentity {A} (subst id refl)
          help {A}{x} = refl

  _prenex:_,_ : ∀ {n} (C : Constraint n Extended) → (m : ℕ) → Constraint (n ⨁ m) Flat → Set
  C prenex: m , C′′ =  ∃ (λ C′ → C ⟶! (Ⅎ′ m · C′) × C′ flatten: C′′)

  prenex : ∀ {n} → (C : Constraint n Extended) → ∃ (λ m → ∃ (λ C′ → C ⟶! (Ⅎ′ m · C′) × ∃ (λ C′′ → C′ flatten: C′′)))
  prenex (QC x) = 0 , _ , PN-QC , _ , FL-QC
  prenex {n} (a ∧′ b) with prenex a | prenex b
  ... | na , a′ , p₁ , a′′ , p₁′ | nb , b′ , p₂ , b′′ , p₂′ 
      = (na + nb) 
      , subst (λ x → Constraint x Extended) (sym (PlusN-collect {n}{na}{nb})) 
              (Constraint-f.map (PlusN-m.unit nb) a′ ∧′ Constraint-f.map (PlusN-f.map nb (PlusN-m.unit na)) b′)
      , subst (λ x → (a ∧′ b) ⟶! x) (collectℲ {n}{na}{nb}) (PN-∧ {na = na}{nb} p₁ p₂) 
      , subst (λ x → Constraint x Flat) (sym (PlusN-collect {n}{na}{nb})) (Constraint-f.map (PlusN-m.unit nb) a′′ ∧′ Constraint-f.map (PlusN-f.map nb (PlusN-m.unit na)) b′′) 
      , subst id (sym (cong₂ (λ it it′ → it  (Constraint-f.map (PlusN-m.unit nb) a′  ∧′ Constraint-f.map (PlusN-f.map nb (PlusN-m.unit na)) b′ )
                                flatten: it′ (Constraint-f.map (PlusN-m.unit nb) a′′ ∧′ Constraint-f.map (PlusN-f.map nb (PlusN-m.unit na)) b′′) ) 
                             (extensionality ((λ x → subst-is-fmap {_}{_}{sym (PlusN-collect {n}{na}{nb})}{C = x}))) 
                             (extensionality ((λ x → subst-is-fmap {_}{_}{sym (PlusN-collect {n}{na}{nb})}{C = x})))))
                 (flatten-fmap (FL-∧ (flatten-fmap p₁′) (flatten-fmap p₂′)))
   where open ≡-Reasoning
  prenex {n} (Imp′ q c) with prenex c
  ... | m , c′ , p , c′′ , p′ = 0 , _ , PN-Imp {m = m} p , _ , FL-Imp {n}{m}{q}{c′}{c′′}
  prenex (Ⅎ_ x) with prenex x
  ... | n , x′ , p , c′′ , p′ = suc n , x′ ,  PN-Frs p , c′′ , p′