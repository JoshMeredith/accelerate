{-# LANGUAGE MagicHash #-}

module Test where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Either
import Data.Array.Accelerate.Smart (match)

import Data.Array.Accelerate.Interpreter

main :: IO ()
main = do
  let
    exprs = fromList (Z :. 2) [Left 1, Right ()] :: Vector (Either Int ())

  print (A.map eitherToBool $ use exprs)

eitherToBool :: (Elt a, Elt b) => Exp (Either a b) -> Exp Bool
eitherToBool = match go
  where
    go (Left#  _) = constant True
    go (Right# _) = constant False
