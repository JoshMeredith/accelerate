{-# LANGUAGE MagicHash, FlexibleContexts #-}

module Test where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Either
import Data.Array.Accelerate.Smart (match)

import Data.Array.Accelerate.Interpreter

main :: IO ()
main = do
  let
    exprs = fromList (Z :. 2) [Left 1, Right ()] :: Vector (Either Int ())

  print (A.map fn $ use exprs)
  print . run $ A.map fn $ use exprs


fn :: Exp (Either Int ()) -> Exp Int
fn = match go
  where
    go (Left#  x) = x + 1
    go (Right# _) = 0
