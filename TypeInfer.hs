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


unify_one :: (Type, Type) -> Subst
unify_one (tau, (TVar t)) =
    if (occursIn (TVar t) tau)
    then throw TypeCircularity
    else [(t, tau)]
unify_one ((TVar t), tau) = 
    if (occursIn (TVar t) tau)
    then throw TypeCircularity
    else [(t, tau)]
unify_one ((TBase a), (TBase b)) =
    if a == b
    then [ ]
    else throw (TypeMismatch (TBase a) (TBase b))
unify_one ((TArrow t11 t12), (TArrow t21 t22)) =
    let s1 = unify_one (t11, t21)
        s2 = unify_one ((applySubst t12 s1), (applySubst t22 s1))
    in (s2 ++ s1)
unify_one (tau_1, tau_2) = throw (TypeMismatch tau_1 tau_2)

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

