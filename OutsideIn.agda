open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn(x : X) where
   open X (x) public
   open import OutsideIn.Prelude public
   open import Data.Vec public hiding ([_]) 
   open import Data.Product public using (∃; _,_) 
   import OutsideIn.Constraints as C
   import OutsideIn.TypeSchema as TS
   import OutsideIn.Expressions as E
   import OutsideIn.Inference.ConstraintGen as CG
   import OutsideIn.Inference.Prenexer as P
   import OutsideIn.Inference.Separator as S
   open E (x) public
   open TS(x) public
   open C (x)
   open CG(x)
   open P (x)
   open S (x)

   go : {ev : Set}{tv : Set}{r : Shape}(Γ : ∀ {x} → Name ev x → TypeSchema tv x)(e : Expression ev tv r)(τ : Type tv) 
                → ∃ (λ m → SeparatedConstraint (tv ⨁ m)) 
   go Γ e τ with prenex (genConstraint Γ e τ)
   ... | m , c = m , separate c



   

--   open import OutsideIn.Types public
--   import OutsideIn.Inference.Simplifier as S   
--   open S(dc) public

--   open C(dc) public
--   open P(dc) public


   