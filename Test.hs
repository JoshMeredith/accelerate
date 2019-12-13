{-# LANGUAGE MagicHash, FlexibleContexts, BlockArguments, LambdaCase #-}

module Test where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Either
import Data.Array.Accelerate.Smart (match)

import Data.Array.Accelerate.Interpreter

main :: IO ()
main = do
  let
    exprs = fromList (Z :. 2) [Left (Left 1), Right ()] :: Vector (Either (Either Int Int) ())

  -- print (A.map fn $ use exprs)
  -- print . run $ A.map fn $ use exprs
  print (match m)


fn :: Exp (Either (Either Int Int) ()) -> Exp Int
fn = match go
  where
    go (Left_  x) = x & match \case
      Left_  y -> 2 + y
      Right_ y -> 3 + y
    go (Right_ _) = 0
    -- go _ = 5

(&) = flip ($)

h :: Exp (Either Int Int) -> Exp (Either () ()) -> Exp Int
h (Left_  _) (Left_  _) = 0
h (Left_  _) (Right_ _) = 1
h (Right_ _) (Left_  _) = 2
h (Right_ _) (Right_ _) = 3

m :: Exp (Either Int Int) -> Exp Int -> Exp (Either () ()) -> Exp Int
m (Left_  _) n (Left_  _) = n + 0
m (Left_  _) n (Right_ _) = n + 1
m (Right_ _) n (Left_  _) = n + 2
m (Right_ _) n (Right_ _) = n + 3
