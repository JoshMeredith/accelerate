{-# LANGUAGE MagicHash, FlexibleContexts, BlockArguments, LambdaCase #-}
{-# OPTIONS_GHC -Wall #-}

module Test where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Data.Either
import Data.Array.Accelerate.Smart (match)

import Data.Array.Accelerate.Interpreter
import Data.Array.Accelerate.Array.Sugar (vary)

main :: IO ()
main = do
  let
    exprs = fromList (Z :. 2) [Left (Left 1), Right ()] :: Vector (Either (Either Int Int) ())

  -- print (A.map fn $ use exprs)
  -- print . run $ A.map fn $ use exprs
  print (match f)


printVary :: Elt t => Exp t -> IO ()
printVary x = case vary x of
  Nothing -> print "No variants"
  Just (m, vs) -> do
    putStrLn "------"
    print m
    putStrLn "---"
    mapM_ (\(t, x) -> print t >> print x >> putStrLn "---") vs
    putStrLn "------"


fn :: Exp (Either (Either Int Int) ()) -> Exp Int
fn = match go
  where
    go (Left_  x) = switch x \case
      Left_  y -> 2 + y
      Right_ y -> 3 + y
    go (Right_ _) = 0
    -- go _ = 5

fn2 :: Exp (Either (Either Int Int) ()) -> Exp Int
fn2 = match go
  where
    go (Left_  x) = case x of
      Left_  y -> 2 + y
      Right_ y -> 3 + y
    go (Right_ _) = 0

-- x = match g (if ... then Left_ (Left 0) else Right_ ())

switch = flip match

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

f :: Exp (Either (Either Int Int) ())
  -> Exp Int
  -> Exp (Either (Either () ()) (Either () ()))
  -> Exp Int
f (Left_ (Left_  n)) m (Left_  _) = 0 + n + m
f (Left_ (Right_ n)) m (Left_  _) = 1 + n + m
f (Right_ _        ) m (Left_  _) = 2     + m
f (Left_ (Left_  n)) m (Right_ _) = 3 + n + m
f (Left_ (Right_ n)) m (Right_ _) = 4 + n + m
f (Right_ _        ) m (Right_ _) = 5     + m
f _ _ (Left_ _) = 6
f _ _ (Right_ _) = 7

g :: Exp (Either (Either Int Int) ())
  -> Exp Int
g (Left_ (Left_  n)) = 0
g (Left_ (Right_ n)) = 1
g (Right_ _        ) = 2
