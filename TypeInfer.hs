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


{-
applySubsOnTVar ::  Subst -> (String, Type) -> ConstraintEnv

applySubsOnGamma :: Subst -> ConstraintEnv -> ConstraintEnv
applySubsOnGamma subs cenv =
  let cenv' = CEnv { constraints = constraints cenv
                   , var = var cenv
                   , tenv = foldr applySubsOnTVar subs (tenv cenv)}
  in cenv'

applySubsOnGamma Subst Tenv
-}

findInEnv :: TEnv -> Tvar -> Type
findInEnv ((head_var, head_type):tail) var =
  if var == head_var
  then head_type
  else findInEnv tail var
findInEnv [] var = throw (UnboundVar var)

{- Performs type inference. -}
inferTypes :: ConstraintEnv -> Exp -> (ConstraintEnv, Subst, Type)
inferTypes cenv (EVar var) =
  let t = findInEnv (tenv cenv) var
  in (cenv, [], t)
inferTypes cenv (ELambda v body) =
  let (tv, cenv1) = newTVar cenv
      (cenv2, s1, t1) = (inferTypes cenv1 body)
  in (cenv2, s1, (applySubst (TArrow tv t1) s1)
inferTypes cenv (EApp fn arg) =
  let (tv, cenv1) = newTVar cenv
      (cenv2, s1, t1) = (inferTypes cenv1 fn)
      (cenv3, s2, t2) = (inferTypes (applySubsOnGamma s1 cenv2) arg)
      s3 = (unify_one (applySubst t1 s2), (TArrow t2 tv)))
  in (s3 ++ s2 ++ s1, apply s3 tv)
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
inferTypes cenv (EPrim (PNum _)) = (cenv, [], intType)
inferTypes cenv (EPrim (PBool _)) = (cenv, [], boolType)
inferTypes cenv (ELet s body) =
  let (cenv1, s1, t1) = inferTypes env s
      cenv2 = applySubsOnGamma s1 cenv1
      t2 = apply t1 cenv2
      (s2, t2) = inferTypes cenv2
  in (cenv1, s1, t2)

{- Top-level type inference function. I will be calling it on Submitty. -}
inferType :: Exp -> Type
inferType exp = 
  let cenv = CEnv { constraints = []
                   , var = 0
                   , tenv = []}
      (e, s, t) = inferTypes cenv exp
  in t

