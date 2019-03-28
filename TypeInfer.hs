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


applySubsOnGamma :: Subst -> ConstraintEnv -> ConstraintEnv
applySubsOnGamma subs cenv =

{- Performs type inference. -}
inferTypes :: ConstraintEnv -> Exp -> (ConstraintEnv, Subst, Type)
inferTypes cenv (EVar var) = throw ToImplement
inferTypes cenv (ELambda v body) = throw ToImplement
inferTypes cenv (EApp fn arg) = throw ToImplement
inferTypes cenv (ECond pred tbody fbody) =
    let (cenv1, s1, t1) = (inferTypes cenv pred)
        s2 = (unify_one (t1, boolType)) ++ s1
        (cenv2, s3, t2) = (inferTypes (applySubsOnGamma s2 cenv1) tbody)
        s4 = s3 ++ s2
        (cenv3, s5, t3) = (inferTypes (applySubsOnGamma s4 cenv2) fbody)
        s6 = (unify_one (t2, t3)) ++ s5 ++ s4
    in (cenv3, s6, t2)
inferTypes cenv (EPlus op1 op2) =
    let (cenv1, s1, t1) = (inferTypes cenv op1)
        s2 = (unify_one (t1, intType)) ++ s1
        (cenv2, s3, t2) = (inferTypes (applySubsOnGamma s2 cenv1) op2)
        s4 = (unify_one (t2, intType)) ++ s3 ++ s2
    in (cenv2, s4, intType)
inferTypes cenv (EPrim (PNum _)) = throw ToImplement
inferTypes cenv (EPrim (PBool _)) = throw ToImplement
inferTypes cenv (ELet s body) = throw ToImplement

{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = 
  let (s, t) = inferTypes [] exp
  in t

