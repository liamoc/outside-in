open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn(x : X) where
   open X (x) public
   open import OutsideIn.Prelude public
   open import Data.Vec public hiding ([_]) 
   import OutsideIn.Constraints as C
   import OutsideIn.TypeSchema as TS
   import OutsideIn.Expressions as E
   import OutsideIn.Inference.ConstraintGen as CG
   import OutsideIn.Inference.Prenexer as P
   open E (x) public
   open TS(x) public
   open C (x)
   open CG(x)
   open P (x)


--   open import OutsideIn.Types public
--   import OutsideIn.Inference.Simplifier as S   
--   open S(dc) public

--   open C(dc) public
--   open P(dc) public


   