open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Environments(x : X) where
  open import Data.Vec hiding (map)
  import OutsideIn.TypeSchema as TS
  import OutsideIn.Expressions as E
  open TS(x)
  open E(x)
  open X(x)

  private
    module TS-f {x} = Functor(type-schema-is-functor {x})
  

  Environment : Set → Set → Set
  Environment ev tv = ∀ {x} → Name ev x → TypeSchema tv x 

  ⟨_⟩,_ : ∀{ev}{tv} → TypeSchema tv Regular → (∀{x} → Name ev x → TypeSchema tv x) 
        → ∀{x} → Name (Ⓢ ev) x → TypeSchema tv x
  (⟨ τ ⟩, Γ) (N zero) = τ
  (⟨ τ ⟩, Γ) (N (suc n)) = Γ (N n)
  (⟨ τ ⟩, Γ) (DC n) = Γ (DC n)
  
  _↑Γ : {ev tv : Set} → Environment ev tv → Environment ev (Ⓢ tv)
  Γ ↑Γ = TS-f.map suc ∘ Γ


  addAll : ∀{n}{ev}{tv} → Vec (Type tv) n → ( Environment ev tv) → Environment (ev ⨁ n) tv
  addAll [] Γ = Γ 
  addAll (τ ∷ τs) Γ = addAll τs (⟨ ∀′ 0 · ε ⇒ τ ⟩, Γ ) 