{-
  You will be filling in the gaps to implement simple type inference.  Please
  provide an implementation for all functions that raise the "ToImplement"
  exception.

  Feel free to add additional functions as you wish.
 -}
module TypeInfer (inferType) where
import Control.Exception
import Data
import Utils
import Data.List

unify_one :: (Type, Type) -> [(TVar, Type)]
unify_one (TArrow a1 a2, TArrow b1 b2) = do
	s1 <- unify_one (a1, b1)
	s2 <- unify_one (b1, b2)
	return (nub (concat s1 s2))
unify_one ((TVar a) t) = [(a, t)]
unify_one (t (TVar a)) = [(a, t)]
unify_one ((TBase a) (TBase b)) = [ ]

unify :: Constraints -> Subst
unify constraints = nub (concat (map unify_one constraints))

{- Performs type inference. -}
inferTypes :: ConstraintEnv -> Exp -> (ConstraintEnv, Type)
inferTypes cenv (EVar var) = throw ToImplement
inferTypes cenv (ELambda v body) = throw ToImplement
inferTypes cenv (EApp fn arg) = throw ToImplement
inferTypes cenv (ECond pred tbody fbody) = throw ToImplement
inferTypes cenv (EPlus op1 op2) = throw ToImplement
inferTypes cenv (EPrim (PNum _)) = throw ToImplement
inferTypes cenv (EPrim (PBool _)) = throw ToImplement
inferTypes cenv (ELet s body) = throw ToImplement

{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = throw ToImplement

