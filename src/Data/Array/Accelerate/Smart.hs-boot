{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

module Data.Array.Accelerate.Smart where

import Data.Kind

type role Exp nominal
newtype Exp t = Exp (PreExp Acc Exp t)

type role Acc nominal
newtype Acc t = Acc (PreAcc Acc Exp t)

type role PreExp representational representational nominal
data PreExp (acc :: Type -> Type) (exp :: Type -> Type) t

type role PreAcc representational representational nominal
data PreAcc (acc :: Type -> Type) (exp :: Type -> Type) t
